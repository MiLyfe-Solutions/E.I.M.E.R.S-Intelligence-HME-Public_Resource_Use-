import V185TrunkScan23Chunk0222

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1318874 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_1318874 : Nat := 118140960795 + 1318874 * 2 ^ 59
def prefixEnd_1318874 : Nat := 4983230072969 + 3 ^ 40 * 1318874 * 2
def baseEnd_1318874 : Nat := 225738761572659377703205

theorem tailTrace_1318874 : CollatzResearch.WordTrace tailWord_1318874 prefixEnd_1318874 225738761572659377703205 := by
  unfold tailWord_1318874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12025821655988054647894919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32068857749301479061053117 12025821655988054647894919)
  ·
    refine ⟨18038732483982081971842379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12025821655988054647894919 18038732483982081971842379)
    ·
      refine ⟨27058098725973122957763569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18038732483982081971842379 27058098725973122957763569)
      ·
        refine ⟨20293574044479842218322677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27058098725973122957763569 20293574044479842218322677)
        ·
          refine ⟨1902522566669985207967751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20293574044479842218322677 1902522566669985207967751)
          ·
            refine ⟨2853783850004977811951627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902522566669985207967751 2853783850004977811951627)
            ·
              refine ⟨4280675775007466717927441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853783850004977811951627 4280675775007466717927441)
              ·
                refine ⟨3210506831255600038445581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280675775007466717927441 3210506831255600038445581)
                ·
                  refine ⟨1203940061720850014417093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3210506831255600038445581 1203940061720850014417093)
                  ·
                    refine ⟨225738761572659377703205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203940061720850014417093 225738761572659377703205)
                    ·
                      rfl

theorem cell23_1318874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_1318874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318874 prefixEnd_1318874 := by exact prefixLift 1318874
  have htrace : WordTrace (prefixWord ++ tailWord_1318874) baseStart_1318874 baseEnd_1318874 := by
    simpa [prefixWord, tailWord_1318874, baseEnd_1318874] using wordTrace_append hprefix tailTrace_1318874
  have hstable : (prefixWord ++ tailWord_1318874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318874).length < 2 ^ (prefixWord ++ tailWord_1318874).sum := by decide
  have hdescent : baseEnd_1318874 < baseStart_1318874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318937 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 8, 2]
def baseStart_1318937 : Nat := 118140960795 + 1318937 * 2 ^ 59
def prefixEnd_1318937 : Nat := 4983230072969 + 3 ^ 40 * 1318937 * 2
def baseEnd_1318937 : Nat := 677248633999211386621825

theorem tailTrace_1318937 : CollatzResearch.WordTrace tailWord_1318937 prefixEnd_1318937 677248633999211386621825 := by
  unfold tailWord_1318937
  simp only [CollatzResearch.WordTrace]
  refine ⟨48105584422723980351123065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32070389615149320234082043 48105584422723980351123065)
  ·
    refine ⟨36079188317042985263342299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48105584422723980351123065 36079188317042985263342299)
    ·
      refine ⟨54118782475564477895013449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36079188317042985263342299 54118782475564477895013449)
      ·
        refine ⟨40589086856673358421260087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54118782475564477895013449 40589086856673358421260087)
        ·
          refine ⟨60883630285010037631890131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40589086856673358421260087 60883630285010037631890131)
          ·
            refine ⟨91325445427515056447835197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60883630285010037631890131 91325445427515056447835197)
            ·
              refine ⟨34247042035318146167938199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91325445427515056447835197 34247042035318146167938199)
              ·
                refine ⟨51370563052977219251907299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34247042035318146167938199 51370563052977219251907299)
                ·
                  refine ⟨77055844579465828877860949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51370563052977219251907299 77055844579465828877860949)
                  ·
                    refine ⟨902998178665615182162433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77055844579465828877860949 902998178665615182162433)
                    ·
                      refine ⟨677248633999211386621825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902998178665615182162433 677248633999211386621825)
                      ·
                        rfl

theorem cell23_1318937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_1318937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318937 prefixEnd_1318937 := by exact prefixLift 1318937
  have htrace : WordTrace (prefixWord ++ tailWord_1318937) baseStart_1318937 baseEnd_1318937 := by
    simpa [prefixWord, tailWord_1318937, baseEnd_1318937] using wordTrace_append hprefix tailTrace_1318937
  have hstable : (prefixWord ++ tailWord_1318937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318937).length < 2 ^ (prefixWord ++ tailWord_1318937).sum := by decide
  have hdescent : baseEnd_1318937 < baseStart_1318937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318947 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 6, 4]
def baseStart_1318947 : Nat := 118140960795 + 1318947 * 2 ^ 59
def prefixEnd_1318947 : Nat := 4983230072969 + 3 ^ 40 * 1318947 * 2
def baseEnd_1318947 : Nat := 225751256268585449165593

theorem tailTrace_1318947 : CollatzResearch.WordTrace tailWord_1318947 prefixEnd_1318947 225751256268585449165593 := by
  unfold tailWord_1318947
  simp only [CollatzResearch.WordTrace]
  refine ⟨48105949152687752058987095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32070632768458501372658063 48105949152687752058987095)
  ·
    refine ⟨72158923729031628088480643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48105949152687752058987095 72158923729031628088480643)
    ·
      refine ⟨108238385593547442132720965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72158923729031628088480643 108238385593547442132720965)
      ·
        refine ⟨20294697298790145399885181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108238385593547442132720965 20294697298790145399885181)
        ·
          refine ⟨7610511487046304524956943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20294697298790145399885181 7610511487046304524956943)
          ·
            refine ⟨11415767230569456787435415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7610511487046304524956943 11415767230569456787435415)
            ·
              refine ⟨17123650845854185181153123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11415767230569456787435415 17123650845854185181153123)
              ·
                refine ⟨25685476268781277771729685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17123650845854185181153123 25685476268781277771729685)
                ·
                  refine ⟨1204006700099122395549829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25685476268781277771729685 1204006700099122395549829)
                  ·
                    refine ⟨225751256268585449165593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1204006700099122395549829 225751256268585449165593)
                    ·
                      rfl

theorem cell23_1318947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 4].length) (baseStart_1318947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318947 prefixEnd_1318947 := by exact prefixLift 1318947
  have htrace : WordTrace (prefixWord ++ tailWord_1318947) baseStart_1318947 baseEnd_1318947 := by
    simpa [prefixWord, tailWord_1318947, baseEnd_1318947] using wordTrace_append hprefix tailTrace_1318947
  have hstable : (prefixWord ++ tailWord_1318947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318947).length < 2 ^ (prefixWord ++ tailWord_1318947).sum := by decide
  have hdescent : baseEnd_1318947 < baseStart_1318947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318960 : List Nat := [2, 1, 1, 1, 2, 5, 11]
def baseStart_1318960 : Nat := 118140960795 + 1318960 * 2 ^ 59
def prefixEnd_1318960 : Nat := 4983230072969 + 3 ^ 40 * 1318960 * 2
def baseEnd_1318960 : Nat := 8361240050052651810299

theorem tailTrace_1318960 : CollatzResearch.WordTrace tailWord_1318960 prefixEnd_1318960 8361240050052651810299 := by
  unfold tailWord_1318960
  simp only [CollatzResearch.WordTrace]
  refine ⟨24053211650820327639605167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32070948867760436852806889 24053211650820327639605167)
  ·
    refine ⟨36079817476230491459407751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24053211650820327639605167 36079817476230491459407751)
    ·
      refine ⟨54119726214345737189111627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36079817476230491459407751 54119726214345737189111627)
      ·
        refine ⟨81179589321518605783667441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54119726214345737189111627 81179589321518605783667441)
        ·
          refine ⟨60884691991138954337750581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81179589321518605783667441 60884691991138954337750581)
          ·
            refine ⟨5707939874169276969164117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60884691991138954337750581 5707939874169276969164117)
            ·
              refine ⟨8361240050052651810299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5707939874169276969164117 8361240050052651810299)
              ·
                rfl

theorem cell23_1318960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 11].length) (baseStart_1318960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318960 prefixEnd_1318960 := by exact prefixLift 1318960
  have htrace : WordTrace (prefixWord ++ tailWord_1318960) baseStart_1318960 baseEnd_1318960 := by
    simpa [prefixWord, tailWord_1318960, baseEnd_1318960] using wordTrace_append hprefix tailTrace_1318960
  have hstable : (prefixWord ++ tailWord_1318960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318960).length < 2 ^ (prefixWord ++ tailWord_1318960).sum := by decide
  have hdescent : baseEnd_1318960 < baseStart_1318960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318977 : List Nat := [1, 2, 5, 1, 2, 1, 1, 10]
def baseStart_1318977 : Nat := 118140960795 + 1318977 * 2 ^ 59
def prefixEnd_1318977 : Nat := 4983230072969 + 3 ^ 40 * 1318977 * 2
def baseEnd_1318977 : Nat := 25084043452792267782283

theorem tailTrace_1318977 : CollatzResearch.WordTrace tailWord_1318977 prefixEnd_1318977 25084043452792267782283 := by
  unfold tailWord_1318977
  simp only [CollatzResearch.WordTrace]
  refine ⟨48107043342579067182579185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32071362228386044788386123 48107043342579067182579185)
  ·
    refine ⟨36080282506934300386934389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48107043342579067182579185 36080282506934300386934389)
    ·
      refine ⟨3382526485025090661275099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36080282506934300386934389 3382526485025090661275099)
      ·
        refine ⟨5073789727537635991912649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382526485025090661275099 5073789727537635991912649)
        ·
          refine ⟨3805342295653226993934487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5073789727537635991912649 3805342295653226993934487)
          ·
            refine ⟨5708013443479840490901731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805342295653226993934487 5708013443479840490901731)
            ·
              refine ⟨8562020165219760736352597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5708013443479840490901731 8562020165219760736352597)
              ·
                refine ⟨25084043452792267782283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8562020165219760736352597 25084043452792267782283)
                ·
                  rfl

theorem cell23_1318977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 10].length) (baseStart_1318977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318977 prefixEnd_1318977 := by exact prefixLift 1318977
  have htrace : WordTrace (prefixWord ++ tailWord_1318977) baseStart_1318977 baseEnd_1318977 := by
    simpa [prefixWord, tailWord_1318977, baseEnd_1318977] using wordTrace_append hprefix tailTrace_1318977
  have hstable : (prefixWord ++ tailWord_1318977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318977).length < 2 ^ (prefixWord ++ tailWord_1318977).sum := by decide
  have hdescent : baseEnd_1318977 < baseStart_1318977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319004 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1319004 : Nat := 118140960795 + 1319004 * 2 ^ 59
def prefixEnd_1319004 : Nat := 4983230072969 + 3 ^ 40 * 1319004 * 2
def baseEnd_1319004 : Nat := 677283037203062624484017

theorem tailTrace_1319004 : CollatzResearch.WordTrace tailWord_1319004 prefixEnd_1319004 677283037203062624484017 := by
  unfold tailWord_1319004
  simp only [CollatzResearch.WordTrace]
  refine ⟨24054014056740625396906033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32072018742320833862541377 24054014056740625396906033)
  ·
    refine ⟨18040510542555469047679525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24054014056740625396906033 18040510542555469047679525)
    ·
      refine ⟨3382595726729150446439911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18040510542555469047679525 3382595726729150446439911)
      ·
        refine ⟨5073893590093725669659867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382595726729150446439911 5073893590093725669659867)
        ·
          refine ⟨7610840385140588504489801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073893590093725669659867 7610840385140588504489801)
          ·
            refine ⟨5708130288855441378367351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7610840385140588504489801 5708130288855441378367351)
            ·
              refine ⟨8562195433283162067551027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5708130288855441378367351 8562195433283162067551027)
              ·
                refine ⟨12843293149924743101326541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8562195433283162067551027 12843293149924743101326541)
                ·
                  refine ⟨4816234931221778662997453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12843293149924743101326541 4816234931221778662997453)
                  ·
                    refine ⟨1806088099208166998624045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4816234931221778662997453 1806088099208166998624045)
                    ·
                      refine ⟨677283037203062624484017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1806088099208166998624045 677283037203062624484017)
                      ·
                        rfl

theorem cell23_1319004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1319004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319004 prefixEnd_1319004 := by exact prefixLift 1319004
  have htrace : WordTrace (prefixWord ++ tailWord_1319004) baseStart_1319004 baseEnd_1319004 := by
    simpa [prefixWord, tailWord_1319004, baseEnd_1319004] using wordTrace_append hprefix tailTrace_1319004
  have hstable : (prefixWord ++ tailWord_1319004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319004).length < 2 ^ (prefixWord ++ tailWord_1319004).sum := by decide
  have hdescent : baseEnd_1319004 < baseStart_1319004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319037 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1319037 : Nat := 118140960795 + 1319037 * 2 ^ 59
def prefixEnd_1319037 : Nat := 4983230072969 + 3 ^ 40 * 1319037 * 2
def baseEnd_1319037 : Nat := 225766660688220331790455

theorem tailTrace_1319037 : CollatzResearch.WordTrace tailWord_1319037 prefixEnd_1319037 225766660688220331790455 := by
  unfold tailWord_1319037
  simp only [CollatzResearch.WordTrace]
  refine ⟨48109231722361697429763365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32072821148241131619842243 48109231722361697429763365)
  ·
    refine ⟨9020480947942818268080631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48109231722361697429763365 9020480947942818268080631)
    ·
      refine ⟨13530721421914227402120947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9020480947942818268080631 13530721421914227402120947)
      ·
        refine ⟨20296082132871341103181421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13530721421914227402120947 20296082132871341103181421)
        ·
          refine ⟨7611030799826752913693033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20296082132871341103181421 7611030799826752913693033)
          ·
            refine ⟨5708273099870064685269775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7611030799826752913693033 5708273099870064685269775)
            ·
              refine ⟨8562409649805097027904663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5708273099870064685269775 8562409649805097027904663)
              ·
                refine ⟨12843614474707645541856995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8562409649805097027904663 12843614474707645541856995)
                ·
                  refine ⟨19265421712061468312785493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12843614474707645541856995 19265421712061468312785493)
                  ·
                    refine ⟨225766660688220331790455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19265421712061468312785493 225766660688220331790455)
                    ·
                      rfl

theorem cell23_1319037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1319037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319037 prefixEnd_1319037 := by exact prefixLift 1319037
  have htrace : WordTrace (prefixWord ++ tailWord_1319037) baseStart_1319037 baseEnd_1319037 := by
    simpa [prefixWord, tailWord_1319037, baseEnd_1319037] using wordTrace_append hprefix tailTrace_1319037
  have hstable : (prefixWord ++ tailWord_1319037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319037).length < 2 ^ (prefixWord ++ tailWord_1319037).sum := by decide
  have hdescent : baseEnd_1319037 < baseStart_1319037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319047 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1319047 : Nat := 118140960795 + 1319047 * 2 ^ 59
def prefixEnd_1319047 : Nat := 4983230072969 + 3 ^ 40 * 1319047 * 2
def baseEnd_1319047 : Nat := 677305116871205956246319

theorem tailTrace_1319047 : CollatzResearch.WordTrace tailWord_1319047 prefixEnd_1319047 677305116871205956246319 := by
  unfold tailWord_1319047
  simp only [CollatzResearch.WordTrace]
  refine ⟨48109596452325469137627395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32073064301550312758418263 48109596452325469137627395)
  ·
    refine ⟨72164394678488203706441093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48109596452325469137627395 72164394678488203706441093)
    ·
      refine ⟨13530824002216538194957705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72164394678488203706441093 13530824002216538194957705)
      ·
        refine ⟨10148118001662403646218279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13530824002216538194957705 10148118001662403646218279)
        ·
          refine ⟨15222177002493605469327419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148118001662403646218279 15222177002493605469327419)
          ·
            refine ⟨22833265503740408203991129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15222177002493605469327419 22833265503740408203991129)
            ·
              refine ⟨17124949127805306152993347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22833265503740408203991129 17124949127805306152993347)
              ·
                refine ⟨25687423691707959229490021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17124949127805306152993347 25687423691707959229490021)
                ·
                  refine ⟨4816391942195242355529379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25687423691707959229490021 4816391942195242355529379)
                  ·
                    refine ⟨7224587913292863533294069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816391942195242355529379 7224587913292863533294069)
                    ·
                      refine ⟨677305116871205956246319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7224587913292863533294069 677305116871205956246319)
                      ·
                        rfl

theorem cell23_1319047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1319047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319047 prefixEnd_1319047 := by exact prefixLift 1319047
  have htrace : WordTrace (prefixWord ++ tailWord_1319047) baseStart_1319047 baseEnd_1319047 := by
    simpa [prefixWord, tailWord_1319047, baseEnd_1319047] using wordTrace_append hprefix tailTrace_1319047
  have hstable : (prefixWord ++ tailWord_1319047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319047).length < 2 ^ (prefixWord ++ tailWord_1319047).sum := by decide
  have hdescent : baseEnd_1319047 < baseStart_1319047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319061 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_1319061 : Nat := 118140960795 + 1319061 * 2 ^ 59
def prefixEnd_1319061 : Nat := 4983230072969 + 3 ^ 40 * 1319061 * 2
def baseEnd_1319061 : Nat := 677312305600368901471255

theorem tailTrace_1319061 : CollatzResearch.WordTrace tailWord_1319061 prefixEnd_1319061 677312305600368901471255 := by
  unfold tailWord_1319061
  simp only [CollatzResearch.WordTrace]
  refine ⟨48110107074274749528637037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32073404716183166352424691 48110107074274749528637037)
  ·
    refine ⟨18041290152853031073238889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48110107074274749528637037 18041290152853031073238889)
    ·
      refine ⟨13530967614639773304929167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18041290152853031073238889 13530967614639773304929167)
      ·
        refine ⟨20296451421959659957393751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13530967614639773304929167 20296451421959659957393751)
        ·
          refine ⟨30444677132939489936090627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20296451421959659957393751 30444677132939489936090627)
          ·
            refine ⟨45667015699409234904135941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30444677132939489936090627 45667015699409234904135941)
            ·
              refine ⟨8562565443639231544525489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45667015699409234904135941 8562565443639231544525489)
              ·
                refine ⟨6421924082729423658394117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8562565443639231544525489 6421924082729423658394117)
                ·
                  refine ⟨1204110765511766935948897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6421924082729423658394117 1204110765511766935948897)
                  ·
                    refine ⟨903083074133825201961673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204110765511766935948897 903083074133825201961673)
                    ·
                      refine ⟨677312305600368901471255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903083074133825201961673 677312305600368901471255)
                      ·
                        rfl

theorem cell23_1319061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_1319061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319061 prefixEnd_1319061 := by exact prefixLift 1319061
  have htrace : WordTrace (prefixWord ++ tailWord_1319061) baseStart_1319061 baseEnd_1319061 := by
    simpa [prefixWord, tailWord_1319061, baseEnd_1319061] using wordTrace_append hprefix tailTrace_1319061
  have hstable : (prefixWord ++ tailWord_1319061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319061).length < 2 ^ (prefixWord ++ tailWord_1319061).sum := by decide
  have hdescent : baseEnd_1319061 < baseStart_1319061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319095 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 2, 2, 2]
def baseStart_1319095 : Nat := 118140960795 + 1319095 * 2 ^ 59
def prefixEnd_1319095 : Nat := 4983230072969 + 3 ^ 40 * 1319095 * 2
def baseEnd_1319095 : Nat := 677329763942621768446099

theorem tailTrace_1319095 : CollatzResearch.WordTrace tailWord_1319095 prefixEnd_1319095 677329763942621768446099 := by
  unfold tailWord_1319095
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111347156151573335374739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32074231437434382223583159 48111347156151573335374739)
  ·
    refine ⟨72167020734227360003062109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48111347156151573335374739 72167020734227360003062109)
    ·
      refine ⟨27062632775335260001148291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72167020734227360003062109 27062632775335260001148291)
      ·
        refine ⟨40593949163002890001722437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27062632775335260001148291 40593949163002890001722437)
        ·
          refine ⟨7611365468063041875322957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40593949163002890001722437 7611365468063041875322957)
          ·
            refine ⟨2854262050523640703246109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7611365468063041875322957 2854262050523640703246109)
            ·
              refine ⟨1070348268946365263717291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2854262050523640703246109 1070348268946365263717291)
              ·
                refine ⟨1605522403419547895575937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070348268946365263717291 1605522403419547895575937)
                ·
                  refine ⟨1204141802564660921681953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605522403419547895575937 1204141802564660921681953)
                  ·
                    refine ⟨903106351923495691261465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204141802564660921681953 903106351923495691261465)
                    ·
                      refine ⟨677329763942621768446099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903106351923495691261465 677329763942621768446099)
                      ·
                        rfl

theorem cell23_1319095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_1319095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319095 prefixEnd_1319095 := by exact prefixLift 1319095
  have htrace : WordTrace (prefixWord ++ tailWord_1319095) baseStart_1319095 baseEnd_1319095 := by
    simpa [prefixWord, tailWord_1319095, baseEnd_1319095] using wordTrace_append hprefix tailTrace_1319095
  have hstable : (prefixWord ++ tailWord_1319095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319095).length < 2 ^ (prefixWord ++ tailWord_1319095).sum := by decide
  have hdescent : baseEnd_1319095 < baseStart_1319095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319097 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_1319097 : Nat := 118140960795 + 1319097 * 2 ^ 59
def prefixEnd_1319097 : Nat := 4983230072969 + 3 ^ 40 * 1319097 * 2
def baseEnd_1319097 : Nat := 225776930301310253540363

theorem tailTrace_1319097 : CollatzResearch.WordTrace tailWord_1319097 prefixEnd_1319097 225776930301310253540363 := by
  unfold tailWord_1319097
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111420102144327676947545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32074280068096218451298363 48111420102144327676947545)
  ·
    refine ⟨36083565076608245757710659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48111420102144327676947545 36083565076608245757710659)
    ·
      refine ⟨54125347614912368636565989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36083565076608245757710659 54125347614912368636565989)
      ·
        refine ⟨10148502677796069119356123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54125347614912368636565989 10148502677796069119356123)
        ·
          refine ⟨15222754016694103679034185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148502677796069119356123 15222754016694103679034185)
          ·
            refine ⟨11417065512520577759275639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15222754016694103679034185 11417065512520577759275639)
            ·
              refine ⟨17125598268780866638913459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11417065512520577759275639 17125598268780866638913459)
              ·
                refine ⟨25688397403171299958370189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17125598268780866638913459 25688397403171299958370189)
                ·
                  refine ⟨9633149026189237484388821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25688397403171299958370189 9633149026189237484388821)
                  ·
                    refine ⟨225776930301310253540363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9633149026189237484388821 225776930301310253540363)
                    ·
                      rfl

theorem cell23_1319097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_1319097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319097 prefixEnd_1319097 := by exact prefixLift 1319097
  have htrace : WordTrace (prefixWord ++ tailWord_1319097) baseStart_1319097 baseEnd_1319097 := by
    simpa [prefixWord, tailWord_1319097, baseEnd_1319097] using wordTrace_append hprefix tailTrace_1319097
  have hstable : (prefixWord ++ tailWord_1319097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319097).length < 2 ^ (prefixWord ++ tailWord_1319097).sum := by decide
  have hdescent : baseEnd_1319097 < baseStart_1319097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319114 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1319114 : Nat := 118140960795 + 1319114 * 2 ^ 59
def prefixEnd_1319114 : Nat := 4983230072969 + 3 ^ 40 * 1319114 * 2
def baseEnd_1319114 : Nat := 225779840025019064702837

theorem tailTrace_1319114 : CollatzResearch.WordTrace tailWord_1319114 prefixEnd_1319114 225779840025019064702837 := by
  unfold tailWord_1319114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12028010035770684895079099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32074693428721826386877597 12028010035770684895079099)
  ·
    refine ⟨18042015053656027342618649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12028010035770684895079099 18042015053656027342618649)
    ·
      refine ⟨13531511290242020506963987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18042015053656027342618649 13531511290242020506963987)
      ·
        refine ⟨20297266935363030760445981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13531511290242020506963987 20297266935363030760445981)
        ·
          refine ⟨7611475100761136535167243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20297266935363030760445981 7611475100761136535167243)
          ·
            refine ⟨11417212651141704802750865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611475100761136535167243 11417212651141704802750865)
            ·
              refine ⟨8562909488356278602063149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11417212651141704802750865 8562909488356278602063149)
              ·
                refine ⟨3211091058133604475773681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8562909488356278602063149 3211091058133604475773681)
                ·
                  refine ⟨2408318293600203356830261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3211091058133604475773681 2408318293600203356830261)
                  ·
                    refine ⟨225779840025019064702837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2408318293600203356830261 225779840025019064702837)
                    ·
                      rfl

theorem cell23_1319114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1319114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319114 prefixEnd_1319114 := by exact prefixLift 1319114
  have htrace : WordTrace (prefixWord ++ tailWord_1319114) baseStart_1319114 baseEnd_1319114 := by
    simpa [prefixWord, tailWord_1319114, baseEnd_1319114] using wordTrace_append hprefix tailTrace_1319114
  have hstable : (prefixWord ++ tailWord_1319114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319114).length < 2 ^ (prefixWord ++ tailWord_1319114).sum := by decide
  have hdescent : baseEnd_1319114 < baseStart_1319114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319118 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_1319118 : Nat := 118140960795 + 1319118 * 2 ^ 59
def prefixEnd_1319118 : Nat := 4983230072969 + 3 ^ 40 * 1319118 * 2
def baseEnd_1319118 : Nat := 75260174888630575384277

theorem tailTrace_1319118 : CollatzResearch.WordTrace tailWord_1319118 prefixEnd_1319118 75260174888630575384277 := by
  unfold tailWord_1319118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6014023254383531032932751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32074790690045498842308005 6014023254383531032932751)
  ·
    refine ⟨9021034881575296549399127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6014023254383531032932751 9021034881575296549399127)
    ·
      refine ⟨13531552322362944824098691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9021034881575296549399127 13531552322362944824098691)
      ·
        refine ⟨20297328483544417236148037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13531552322362944824098691 20297328483544417236148037)
        ·
          refine ⟨3805749090664578231777757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20297328483544417236148037 3805749090664578231777757)
          ·
            refine ⟨1427155908999216836916659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3805749090664578231777757 1427155908999216836916659)
            ·
              refine ⟨2140733863498825255374989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427155908999216836916659 2140733863498825255374989)
              ·
                refine ⟨802775198812059470765621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2140733863498825255374989 802775198812059470765621)
                ·
                  refine ⟨75260174888630575384277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802775198812059470765621 75260174888630575384277)
                  ·
                    rfl

theorem cell23_1319118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_1319118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319118 prefixEnd_1319118 := by exact prefixLift 1319118
  have htrace : WordTrace (prefixWord ++ tailWord_1319118) baseStart_1319118 baseEnd_1319118 := by
    simpa [prefixWord, tailWord_1319118, baseEnd_1319118] using wordTrace_append hprefix tailTrace_1319118
  have hstable : (prefixWord ++ tailWord_1319118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319118).length < 2 ^ (prefixWord ++ tailWord_1319118).sum := by decide
  have hdescent : baseEnd_1319118 < baseStart_1319118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319171 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 3]
def baseStart_1319171 : Nat := 118140960795 + 1319171 * 2 ^ 59
def prefixEnd_1319171 : Nat := 4983230072969 + 3 ^ 40 * 1319171 * 2
def baseEnd_1319171 : Nat := 677368788472363471095749

theorem tailTrace_1319171 : CollatzResearch.WordTrace tailWord_1319171 prefixEnd_1319171 677368788472363471095749 := by
  unfold tailWord_1319171
  simp only [CollatzResearch.WordTrace]
  refine ⟨48114119103876238315141367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32076079402584158876760911 48114119103876238315141367)
  ·
    refine ⟨72171178655814357472712051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48114119103876238315141367 72171178655814357472712051)
    ·
      refine ⟨108256767983721536209068077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72171178655814357472712051 108256767983721536209068077)
      ·
        refine ⟨40596287993895576078400529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108256767983721536209068077 40596287993895576078400529)
        ·
          refine ⟨30447215995421682058800397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40596287993895576078400529 30447215995421682058800397)
          ·
            refine ⟨11417705998283130772050149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30447215995421682058800397 11417705998283130772050149)
            ·
              refine ⟨2140819874678087019759403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11417705998283130772050149 2140819874678087019759403)
              ·
                refine ⟨3211229812017130529639105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140819874678087019759403 3211229812017130529639105)
                ·
                  refine ⟨2408422359012847897229329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3211229812017130529639105 2408422359012847897229329)
                  ·
                    refine ⟨1806316769259635922921997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2408422359012847897229329 1806316769259635922921997)
                    ·
                      refine ⟨677368788472363471095749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1806316769259635922921997 677368788472363471095749)
                      ·
                        rfl

theorem cell23_1319171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_1319171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319171 prefixEnd_1319171 := by exact prefixLift 1319171
  have htrace : WordTrace (prefixWord ++ tailWord_1319171) baseStart_1319171 baseEnd_1319171 := by
    simpa [prefixWord, tailWord_1319171, baseEnd_1319171] using wordTrace_append hprefix tailTrace_1319171
  have hstable : (prefixWord ++ tailWord_1319171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319171).length < 2 ^ (prefixWord ++ tailWord_1319171).sum := by decide
  have hdescent : baseEnd_1319171 < baseStart_1319171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319191 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 6]
def baseStart_1319191 : Nat := 118140960795 + 1319191 * 2 ^ 59
def prefixEnd_1319191 : Nat := 4983230072969 + 3 ^ 40 * 1319191 * 2
def baseEnd_1319191 : Nat := 75264339787272599205073

theorem tailTrace_1319191 : CollatzResearch.WordTrace tailWord_1319191 prefixEnd_1319191 75264339787272599205073 := by
  unfold tailWord_1319191
  simp only [CollatzResearch.WordTrace]
  refine ⟨48114848563803781730869427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32076565709202521153912951 48114848563803781730869427)
  ·
    refine ⟨72172272845705672596304141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48114848563803781730869427 72172272845705672596304141)
    ·
      refine ⟨27064602317139627223614053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72172272845705672596304141 27064602317139627223614053)
      ·
        refine ⟨5074612934463680104427635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27064602317139627223614053 5074612934463680104427635)
        ·
          refine ⟨7611919401695520156641453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5074612934463680104427635 7611919401695520156641453)
          ·
            refine ⟨2854469775635820058740545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7611919401695520156641453 2854469775635820058740545)
            ·
              refine ⟨2140852331726865044055409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854469775635820058740545 2140852331726865044055409)
              ·
                refine ⟨1605639248795148783041557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140852331726865044055409 1605639248795148783041557)
                ·
                  refine ⟨75264339787272599205073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1605639248795148783041557 75264339787272599205073)
                  ·
                    rfl

theorem cell23_1319191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 6].length) (baseStart_1319191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319191 prefixEnd_1319191 := by exact prefixLift 1319191
  have htrace : WordTrace (prefixWord ++ tailWord_1319191) baseStart_1319191 baseEnd_1319191 := by
    simpa [prefixWord, tailWord_1319191, baseEnd_1319191] using wordTrace_append hprefix tailTrace_1319191
  have hstable : (prefixWord ++ tailWord_1319191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319191).length < 2 ^ (prefixWord ++ tailWord_1319191).sum := by decide
  have hdescent : baseEnd_1319191 < baseStart_1319191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319221 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1319221 : Nat := 118140960795 + 1319221 * 2 ^ 59
def prefixEnd_1319221 : Nat := 4983230072969 + 3 ^ 40 * 1319221 * 2
def baseEnd_1319221 : Nat := 225798154168362758490173

theorem tailTrace_1319221 : CollatzResearch.WordTrace tailWord_1319221 prefixEnd_1319221 225798154168362758490173 := by
  unfold tailWord_1319221
  simp only [CollatzResearch.WordTrace]
  refine ⟨48115942753695096854461517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32077295169130064569641011 48115942753695096854461517)
  ·
    refine ⟨18043478532635661320423069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48115942753695096854461517 18043478532635661320423069)
    ·
      refine ⟨6766304449738372995158651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18043478532635661320423069 6766304449738372995158651)
      ·
        refine ⟨10149456674607559492737977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6766304449738372995158651 10149456674607559492737977)
        ·
          refine ⟨7612092505955669619553483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10149456674607559492737977 7612092505955669619553483)
          ·
            refine ⟨11418138758933504429330225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612092505955669619553483 11418138758933504429330225)
            ·
              refine ⟨8563604069200128321997669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11418138758933504429330225 8563604069200128321997669)
              ·
                refine ⟨1605675762975024060374563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8563604069200128321997669 1605675762975024060374563)
                ·
                  refine ⟨2408513644462536090561845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605675762975024060374563 2408513644462536090561845)
                  ·
                    refine ⟨225798154168362758490173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2408513644462536090561845 225798154168362758490173)
                    ·
                      rfl

theorem cell23_1319221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1319221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319221 prefixEnd_1319221 := by exact prefixLift 1319221
  have htrace : WordTrace (prefixWord ++ tailWord_1319221) baseStart_1319221 baseEnd_1319221 := by
    simpa [prefixWord, tailWord_1319221, baseEnd_1319221] using wordTrace_append hprefix tailTrace_1319221
  have hstable : (prefixWord ++ tailWord_1319221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319221).length < 2 ^ (prefixWord ++ tailWord_1319221).sum := by decide
  have hdescent : baseEnd_1319221 < baseStart_1319221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319251 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 2, 4]
def baseStart_1319251 : Nat := 118140960795 + 1319251 * 2 ^ 59
def prefixEnd_1319251 : Nat := 4983230072969 + 3 ^ 40 * 1319251 * 2
def baseEnd_1319251 : Nat := 225803288974907719365127

theorem tailTrace_1319251 : CollatzResearch.WordTrace tailWord_1319251 prefixEnd_1319251 225803288974907719365127 := by
  unfold tailWord_1319251
  simp only [CollatzResearch.WordTrace]
  refine ⟨48117036943586411978053607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32078024629057607985369071 48117036943586411978053607)
  ·
    refine ⟨72175555415379617967080411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48117036943586411978053607 72175555415379617967080411)
    ·
      refine ⟨108263333123069426950620617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72175555415379617967080411 108263333123069426950620617)
      ·
        refine ⟨81197499842302070212965463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108263333123069426950620617 81197499842302070212965463)
        ·
          refine ⟨121796249763453105319448195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81197499842302070212965463 121796249763453105319448195)
          ·
            refine ⟨182694374645179657979172293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121796249763453105319448195 182694374645179657979172293)
            ·
              refine ⟨34255195245971185871094805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182694374645179657979172293 34255195245971185871094805)
              ·
                refine ⟨1605712277154899337707569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34255195245971185871094805 1605712277154899337707569)
                ·
                  refine ⟨1204284207866174503280677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605712277154899337707569 1204284207866174503280677)
                  ·
                    refine ⟨225803288974907719365127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1204284207866174503280677 225803288974907719365127)
                    ·
                      rfl

theorem cell23_1319251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 4].length) (baseStart_1319251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319251 prefixEnd_1319251 := by exact prefixLift 1319251
  have htrace : WordTrace (prefixWord ++ tailWord_1319251) baseStart_1319251 baseEnd_1319251 := by
    simpa [prefixWord, tailWord_1319251, baseEnd_1319251] using wordTrace_append hprefix tailTrace_1319251
  have hstable : (prefixWord ++ tailWord_1319251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319251).length < 2 ^ (prefixWord ++ tailWord_1319251).sum := by decide
  have hdescent : baseEnd_1319251 < baseStart_1319251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319271 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1319271 : Nat := 118140960795 + 1319271 * 2 ^ 59
def prefixEnd_1319271 : Nat := 4983230072969 + 3 ^ 40 * 1319271 * 2
def baseEnd_1319271 : Nat := 677420136537813079845289

theorem tailTrace_1319271 : CollatzResearch.WordTrace tailWord_1319271 prefixEnd_1319271 677420136537813079845289 := by
  unfold tailWord_1319271
  simp only [CollatzResearch.WordTrace]
  refine ⟨48117766403513955393781667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32078510935675970262521111 48117766403513955393781667)
  ·
    refine ⟨72176649605270933090672501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48117766403513955393781667 72176649605270933090672501)
    ·
      refine ⟨6766560900494149977250547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72176649605270933090672501 6766560900494149977250547)
      ·
        refine ⟨10149841350741224965875821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6766560900494149977250547 10149841350741224965875821)
        ·
          refine ⟨3806190506527959362203433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10149841350741224965875821 3806190506527959362203433)
          ·
            refine ⟨2854642879895969521652575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3806190506527959362203433 2854642879895969521652575)
            ·
              refine ⟨4281964319843954282478863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854642879895969521652575 4281964319843954282478863)
              ·
                refine ⟨6422946479765931423718295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281964319843954282478863 6422946479765931423718295)
                ·
                  refine ⟨9634419719648897135577443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422946479765931423718295 9634419719648897135577443)
                  ·
                    refine ⟨14451629579473345703366165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9634419719648897135577443 14451629579473345703366165)
                    ·
                      refine ⟨677420136537813079845289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14451629579473345703366165 677420136537813079845289)
                      ·
                        rfl

theorem cell23_1319271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1319271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319271 prefixEnd_1319271 := by exact prefixLift 1319271
  have htrace : WordTrace (prefixWord ++ tailWord_1319271) baseStart_1319271 baseEnd_1319271 := by
    simpa [prefixWord, tailWord_1319271, baseEnd_1319271] using wordTrace_append hprefix tailTrace_1319271
  have hstable : (prefixWord ++ tailWord_1319271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319271).length < 2 ^ (prefixWord ++ tailWord_1319271).sum := by decide
  have hdescent : baseEnd_1319271 < baseStart_1319271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319286 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1319286 : Nat := 118140960795 + 1319286 * 2 ^ 59
def prefixEnd_1319286 : Nat := 4983230072969 + 3 ^ 40 * 1319286 * 2
def baseEnd_1319286 : Nat := 677427838747630521157721

theorem tailTrace_1319286 : CollatzResearch.WordTrace tailWord_1319286 prefixEnd_1319286 677427838747630521157721 := by
  unfold tailWord_1319286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007394593653725809723607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32078875665639741970385141 3007394593653725809723607)
  ·
    refine ⟨4511091890480588714585411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3007394593653725809723607 4511091890480588714585411)
    ·
      refine ⟨6766637835720883071878117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4511091890480588714585411 6766637835720883071878117)
      ·
        refine ⟨1268744594197665575977147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6766637835720883071878117 1268744594197665575977147)
        ·
          refine ⟨1903116891296498363965721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268744594197665575977147 1903116891296498363965721)
          ·
            refine ⟨1427337668472373772974291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1903116891296498363965721 1427337668472373772974291)
            ·
              refine ⟨2141006502708560659461437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427337668472373772974291 2141006502708560659461437)
              ·
                refine ⟨802877438515710247298039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2141006502708560659461437 802877438515710247298039)
                ·
                  refine ⟨1204316157773565370947059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802877438515710247298039 1204316157773565370947059)
                  ·
                    refine ⟨1806474236660348056420589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1204316157773565370947059 1806474236660348056420589)
                    ·
                      refine ⟨677427838747630521157721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1806474236660348056420589 677427838747630521157721)
                      ·
                        rfl

theorem cell23_1319286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1319286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319286 prefixEnd_1319286 := by exact prefixLift 1319286
  have htrace : WordTrace (prefixWord ++ tailWord_1319286) baseStart_1319286 baseEnd_1319286 := by
    simpa [prefixWord, tailWord_1319286, baseEnd_1319286] using wordTrace_append hprefix tailTrace_1319286
  have hstable : (prefixWord ++ tailWord_1319286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319286).length < 2 ^ (prefixWord ++ tailWord_1319286).sum := by decide
  have hdescent : baseEnd_1319286 < baseStart_1319286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319308 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_1319308 : Nat := 118140960795 + 1319308 * 2 ^ 59
def prefixEnd_1319308 : Nat := 4983230072969 + 3 ^ 40 * 1319308 * 2
def baseEnd_1319308 : Nat := 677439135322029435082619

theorem tailTrace_1319308 : CollatzResearch.WordTrace tailWord_1319308 prefixEnd_1319308 677439135322029435082619 := by
  unfold tailWord_1319308
  simp only [CollatzResearch.WordTrace]
  refine ⟨24059557952189955356439289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32079410602919940475252385 24059557952189955356439289)
  ·
    refine ⟨18044668464142466517329467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24059557952189955356439289 18044668464142466517329467)
    ·
      refine ⟨27067002696213699775994201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18044668464142466517329467 27067002696213699775994201)
      ·
        refine ⟨20300252022160274831995651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27067002696213699775994201 20300252022160274831995651)
        ·
          refine ⟨30450378033240412247993477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20300252022160274831995651 30450378033240412247993477)
          ·
            refine ⟨5709445881232577296498777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30450378033240412247993477 5709445881232577296498777)
            ·
              refine ⟨4282084410924432972374083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5709445881232577296498777 4282084410924432972374083)
              ·
                refine ⟨6423126616386649458561125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282084410924432972374083 6423126616386649458561125)
                ·
                  refine ⟨1204336240572496773480211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6423126616386649458561125 1204336240572496773480211)
                  ·
                    refine ⟨1806504360858745160220317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1204336240572496773480211 1806504360858745160220317)
                    ·
                      refine ⟨677439135322029435082619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1806504360858745160220317 677439135322029435082619)
                      ·
                        rfl

theorem cell23_1319308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_1319308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319308 prefixEnd_1319308 := by exact prefixLift 1319308
  have htrace : WordTrace (prefixWord ++ tailWord_1319308) baseStart_1319308 baseEnd_1319308 := by
    simpa [prefixWord, tailWord_1319308, baseEnd_1319308] using wordTrace_append hprefix tailTrace_1319308
  have hstable : (prefixWord ++ tailWord_1319308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319308).length < 2 ^ (prefixWord ++ tailWord_1319308).sum := by decide
  have hdescent : baseEnd_1319308 < baseStart_1319308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319329 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1319329 : Nat := 118140960795 + 1319329 * 2 ^ 59
def prefixEnd_1319329 : Nat := 4983230072969 + 3 ^ 40 * 1319329 * 2
def baseEnd_1319329 : Nat := 677449918415773852920023

theorem tailTrace_1319329 : CollatzResearch.WordTrace tailWord_1319329 prefixEnd_1319329 677449918415773852920023 := by
  unfold tailWord_1319329
  simp only [CollatzResearch.WordTrace]
  refine ⟨48119881837303831299393041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32079921224869220866262027 48119881837303831299393041)
  ·
    refine ⟨36089911377977873474544781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48119881837303831299393041 36089911377977873474544781)
    ·
      refine ⟨13533716766741702552954293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36089911377977873474544781 13533716766741702552954293)
      ·
        refine ⟨1268785946882034614339465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13533716766741702552954293 1268785946882034614339465)
        ·
          refine ⟨951589460161525960754599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1268785946882034614339465 951589460161525960754599)
          ·
            refine ⟨1427384190242288941131899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951589460161525960754599 1427384190242288941131899)
            ·
              refine ⟨2141076285363433411697849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427384190242288941131899 2141076285363433411697849)
              ·
                refine ⟨1605807214022575058773387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141076285363433411697849 1605807214022575058773387)
                ·
                  refine ⟨2408710821033862588160081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605807214022575058773387 2408710821033862588160081)
                  ·
                    refine ⟨1806533115775396941120061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2408710821033862588160081 1806533115775396941120061)
                    ·
                      refine ⟨677449918415773852920023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1806533115775396941120061 677449918415773852920023)
                      ·
                        rfl

theorem cell23_1319329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1319329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319329 prefixEnd_1319329 := by exact prefixLift 1319329
  have htrace : WordTrace (prefixWord ++ tailWord_1319329) baseStart_1319329 baseEnd_1319329 := by
    simpa [prefixWord, tailWord_1319329, baseEnd_1319329] using wordTrace_append hprefix tailTrace_1319329
  have hstable : (prefixWord ++ tailWord_1319329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319329).length < 2 ^ (prefixWord ++ tailWord_1319329).sum := by decide
  have hdescent : baseEnd_1319329 < baseStart_1319329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319335 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1319335 : Nat := 118140960795 + 1319335 * 2 ^ 59
def prefixEnd_1319335 : Nat := 4983230072969 + 3 ^ 40 * 1319335 * 2
def baseEnd_1319335 : Nat := 677452999299700829444995

theorem tailTrace_1319335 : CollatzResearch.WordTrace tailWord_1319335 prefixEnd_1319335 677452999299700829444995 := by
  unfold tailWord_1319335
  simp only [CollatzResearch.WordTrace]
  refine ⟨48120100675282094324111459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32080067116854729549407639 48120100675282094324111459)
  ·
    refine ⟨72180151012923141486167189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48120100675282094324111459 72180151012923141486167189)
    ·
      refine ⟨3383444578730772257164087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72180151012923141486167189 3383444578730772257164087)
      ·
        refine ⟨5075166868096158385746131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383444578730772257164087 5075166868096158385746131)
        ·
          refine ⟨7612750302144237578619197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075166868096158385746131 7612750302144237578619197)
          ·
            refine ⟨2854781363304089091982199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7612750302144237578619197 2854781363304089091982199)
            ·
              refine ⟨4282172044956133637973299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854781363304089091982199 4282172044956133637973299)
              ·
                refine ⟨6423258067434200456959949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282172044956133637973299 6423258067434200456959949)
                ·
                  refine ⟨2408721775287825171359981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6423258067434200456959949 2408721775287825171359981)
                  ·
                    refine ⟨903270665732934439259993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408721775287825171359981 903270665732934439259993)
                    ·
                      refine ⟨677452999299700829444995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903270665732934439259993 677452999299700829444995)
                      ·
                        rfl

theorem cell23_1319335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1319335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319335 prefixEnd_1319335 := by exact prefixLift 1319335
  have htrace : WordTrace (prefixWord ++ tailWord_1319335) baseStart_1319335 baseEnd_1319335 := by
    simpa [prefixWord, tailWord_1319335, baseEnd_1319335] using wordTrace_append hprefix tailTrace_1319335
  have hstable : (prefixWord ++ tailWord_1319335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319335).length < 2 ^ (prefixWord ++ tailWord_1319335).sum := by decide
  have hdescent : baseEnd_1319335 < baseStart_1319335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319344 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1319344 : Nat := 118140960795 + 1319344 * 2 ^ 59
def prefixEnd_1319344 : Nat := 4983230072969 + 3 ^ 40 * 1319344 * 2
def baseEnd_1319344 : Nat := 677457620625591294232453

theorem tailTrace_1319344 : CollatzResearch.WordTrace tailWord_1319344 prefixEnd_1319344 677457620625591294232453 := by
  unfold tailWord_1319344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060214466124744430594543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32080285954832992574126057 24060214466124744430594543)
  ·
    refine ⟨36090321699187116645891815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24060214466124744430594543 36090321699187116645891815)
    ·
      refine ⟨54135482548780674968837723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36090321699187116645891815 54135482548780674968837723)
      ·
        refine ⟨81203223823171012453256585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54135482548780674968837723 81203223823171012453256585)
        ·
          refine ⟨60902417867378259339942439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81203223823171012453256585 60902417867378259339942439)
          ·
            refine ⟨91353626801067389009913659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60902417867378259339942439 91353626801067389009913659)
            ·
              refine ⟨137030440201601083514870489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91353626801067389009913659 137030440201601083514870489)
              ·
                refine ⟨102772830151200812636152867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137030440201601083514870489 102772830151200812636152867)
                ·
                  refine ⟨154159245226801218954229301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102772830151200812636152867 154159245226801218954229301)
                  ·
                    refine ⟨14452429240012614276958997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154159245226801218954229301 14452429240012614276958997)
                    ·
                      refine ⟨677457620625591294232453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14452429240012614276958997 677457620625591294232453)
                      ·
                        rfl

theorem cell23_1319344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1319344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319344 prefixEnd_1319344 := by exact prefixLift 1319344
  have htrace : WordTrace (prefixWord ++ tailWord_1319344) baseStart_1319344 baseEnd_1319344 := by
    simpa [prefixWord, tailWord_1319344, baseEnd_1319344] using wordTrace_append hprefix tailTrace_1319344
  have hstable : (prefixWord ++ tailWord_1319344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319344).length < 2 ^ (prefixWord ++ tailWord_1319344).sum := by decide
  have hdescent : baseEnd_1319344 < baseStart_1319344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319351 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_1319351 : Nat := 118140960795 + 1319351 * 2 ^ 59
def prefixEnd_1319351 : Nat := 4983230072969 + 3 ^ 40 * 1319351 * 2
def baseEnd_1319351 : Nat := 677461214990172766844921

theorem tailTrace_1319351 : CollatzResearch.WordTrace tailWord_1319351 prefixEnd_1319351 677461214990172766844921 := by
  unfold tailWord_1319351
  simp only [CollatzResearch.WordTrace]
  refine ⟨48120684243224129056693907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32080456162149419371129271 48120684243224129056693907)
  ·
    refine ⟨72181026364836193585040861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48120684243224129056693907 72181026364836193585040861)
    ·
      refine ⟨27067884886813572594390323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72181026364836193585040861 27067884886813572594390323)
      ·
        refine ⟨40601827330220358891585485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27067884886813572594390323 40601827330220358891585485)
        ·
          refine ⟨15225685248832634584344557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40601827330220358891585485 15225685248832634584344557)
          ·
            refine ⟨5709631968312237969129209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15225685248832634584344557 5709631968312237969129209)
            ·
              refine ⟨4282223976234178476846907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5709631968312237969129209 4282223976234178476846907)
              ·
                refine ⟨6423335964351267715270361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282223976234178476846907 6423335964351267715270361)
                ·
                  refine ⟨4817501973263450786452771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6423335964351267715270361 4817501973263450786452771)
                  ·
                    refine ⟨7226252959895176179679157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817501973263450786452771 7226252959895176179679157)
                    ·
                      refine ⟨677461214990172766844921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7226252959895176179679157 677461214990172766844921)
                      ·
                        rfl

theorem cell23_1319351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_1319351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319351 prefixEnd_1319351 := by exact prefixLift 1319351
  have htrace : WordTrace (prefixWord ++ tailWord_1319351) baseStart_1319351 baseEnd_1319351 := by
    simpa [prefixWord, tailWord_1319351, baseEnd_1319351] using wordTrace_append hprefix tailTrace_1319351
  have hstable : (prefixWord ++ tailWord_1319351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319351).length < 2 ^ (prefixWord ++ tailWord_1319351).sum := by decide
  have hdescent : baseEnd_1319351 < baseStart_1319351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319382 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1319382 : Nat := 118140960795 + 1319382 * 2 ^ 59
def prefixEnd_1319382 : Nat := 4983230072969 + 3 ^ 40 * 1319382 * 2
def baseEnd_1319382 : Nat := 677477132890462145557279

theorem tailTrace_1319382 : CollatzResearch.WordTrace tailWord_1319382 prefixEnd_1319382 677477132890462145557279 := by
  unfold tailWord_1319382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007613431631988834442025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32081209937407880900714933 3007613431631988834442025)
  ·
    refine ⟨2255710073723991625831519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3007613431631988834442025 2255710073723991625831519)
    ·
      refine ⟨3383565110585987438747279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255710073723991625831519 3383565110585987438747279)
      ·
        refine ⟨5075347665878981158120919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383565110585987438747279 5075347665878981158120919)
        ·
          refine ⟨7613021498818471737181379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075347665878981158120919 7613021498818471737181379)
          ·
            refine ⟨11419532248227707605772069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613021498818471737181379 11419532248227707605772069)
            ·
              refine ⟨2141162296542695176082263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11419532248227707605772069 2141162296542695176082263)
              ·
                refine ⟨3211743444814042764123395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141162296542695176082263 3211743444814042764123395)
                ·
                  refine ⟨4817615167221064146185093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211743444814042764123395 4817615167221064146185093)
                  ·
                    refine ⟨903302843853949527409705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4817615167221064146185093 903302843853949527409705)
                    ·
                      refine ⟨677477132890462145557279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903302843853949527409705 677477132890462145557279)
                      ·
                        rfl

theorem cell23_1319382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1319382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319382 prefixEnd_1319382 := by exact prefixLift 1319382
  have htrace : WordTrace (prefixWord ++ tailWord_1319382) baseStart_1319382 baseEnd_1319382 := by
    simpa [prefixWord, tailWord_1319382, baseEnd_1319382] using wordTrace_append hprefix tailTrace_1319382
  have hstable : (prefixWord ++ tailWord_1319382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319382).length < 2 ^ (prefixWord ++ tailWord_1319382).sum := by decide
  have hdescent : baseEnd_1319382 < baseStart_1319382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319401 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_1319401 : Nat := 118140960795 + 1319401 * 2 ^ 59
def prefixEnd_1319401 : Nat := 4983230072969 + 3 ^ 40 * 1319401 * 2
def baseEnd_1319401 : Nat := 225828963007632523739897

theorem tailTrace_1319401 : CollatzResearch.WordTrace tailWord_1319401 prefixEnd_1319401 225828963007632523739897 := by
  unfold tailWord_1319401
  simp only [CollatzResearch.WordTrace]
  refine ⟨48122507893042987596014057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32081671928695325064009371 48122507893042987596014057)
  ·
    refine ⟨36091880919782240697010543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48122507893042987596014057 36091880919782240697010543)
    ·
      refine ⟨54137821379673361045515815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36091880919782240697010543 54137821379673361045515815)
      ·
        refine ⟨81206732069510041568273723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54137821379673361045515815 81206732069510041568273723)
        ·
          refine ⟨121810098104265062352410585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81206732069510041568273723 121810098104265062352410585)
          ·
            refine ⟨91357573578198796764307939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121810098104265062352410585 91357573578198796764307939)
            ·
              refine ⟨137036360367298195146461909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91357573578198796764307939 137036360367298195146461909)
              ·
                refine ⟨3211789696108551448745201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137036360367298195146461909 3211789696108551448745201)
                ·
                  refine ⟨2408842272081413586558901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3211789696108551448745201 2408842272081413586558901)
                  ·
                    refine ⟨225828963007632523739897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2408842272081413586558901 225828963007632523739897)
                    ·
                      rfl

theorem cell23_1319401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_1319401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319401 prefixEnd_1319401 := by exact prefixLift 1319401
  have htrace : WordTrace (prefixWord ++ tailWord_1319401) baseStart_1319401 baseEnd_1319401 := by
    simpa [prefixWord, tailWord_1319401, baseEnd_1319401] using wordTrace_append hprefix tailTrace_1319401
  have hstable : (prefixWord ++ tailWord_1319401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319401).length < 2 ^ (prefixWord ++ tailWord_1319401).sum := by decide
  have hdescent : baseEnd_1319401 < baseStart_1319401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319405 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1319405 : Nat := 118140960795 + 1319405 * 2 ^ 59
def prefixEnd_1319405 : Nat := 4983230072969 + 3 ^ 40 * 1319405 * 2
def baseEnd_1319405 : Nat := 75276549216168395063297

theorem tailTrace_1319405 : CollatzResearch.WordTrace tailWord_1319405 prefixEnd_1319405 75276549216168395063297 := by
  unfold tailWord_1319405
  simp only [CollatzResearch.WordTrace]
  refine ⟨48122653785028496279159669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32081769190018997519439779 48122653785028496279159669)
  ·
    refine ⟨4511498792346421526171219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48122653785028496279159669 4511498792346421526171219)
    ·
      refine ⟨6767248188519632289256829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4511498792346421526171219 6767248188519632289256829)
      ·
        refine ⟨2537718070694862108471311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6767248188519632289256829 2537718070694862108471311)
        ·
          refine ⟨3806577106042293162706967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537718070694862108471311 3806577106042293162706967)
          ·
            refine ⟨5709865659063439744060451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806577106042293162706967 5709865659063439744060451)
            ·
              refine ⟨8564798488595159616090677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5709865659063439744060451 8564798488595159616090677)
              ·
                refine ⟨802949858305796214008501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8564798488595159616090677 802949858305796214008501)
                ·
                  refine ⟨75276549216168395063297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802949858305796214008501 75276549216168395063297)
                  ·
                    rfl

theorem cell23_1319405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1319405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319405 prefixEnd_1319405 := by exact prefixLift 1319405
  have htrace : WordTrace (prefixWord ++ tailWord_1319405) baseStart_1319405 baseEnd_1319405 := by
    simpa [prefixWord, tailWord_1319405, baseEnd_1319405] using wordTrace_append hprefix tailTrace_1319405
  have hstable : (prefixWord ++ tailWord_1319405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319405).length < 2 ^ (prefixWord ++ tailWord_1319405).sum := by decide
  have hdescent : baseEnd_1319405 < baseStart_1319405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319438 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1319438 : Nat := 118140960795 + 1319438 * 2 ^ 59
def prefixEnd_1319438 : Nat := 4983230072969 + 3 ^ 40 * 1319438 * 2
def baseEnd_1319438 : Nat := 677505887807113926457021

theorem tailTrace_1319438 : CollatzResearch.WordTrace tailWord_1319438 prefixEnd_1319438 677505887807113926457021 := by
  unfold tailWord_1319438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015482174238617864388871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32082571595939295276740645 6015482174238617864388871)
  ·
    refine ⟨9023223261357926796583307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015482174238617864388871 9023223261357926796583307)
    ·
      refine ⟨13534834892036890194874961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9023223261357926796583307 13534834892036890194874961)
      ·
        refine ⟨10151126169027667646156221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13534834892036890194874961 10151126169027667646156221)
        ·
          refine ⟨3806672313385375367308583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10151126169027667646156221 3806672313385375367308583)
          ·
            refine ⟨5710008470078063050962875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806672313385375367308583 5710008470078063050962875)
            ·
              refine ⟨8565012705117094576444313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710008470078063050962875 8565012705117094576444313)
              ·
                refine ⟨6423759528837820932333235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8565012705117094576444313 6423759528837820932333235)
                ·
                  refine ⟨9635639293256731398499853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6423759528837820932333235 9635639293256731398499853)
                  ·
                    refine ⟨3613364734971274274437445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9635639293256731398499853 3613364734971274274437445)
                    ·
                      refine ⟨677505887807113926457021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3613364734971274274437445 677505887807113926457021)
                      ·
                        rfl

theorem cell23_1319438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1319438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319438 prefixEnd_1319438 := by exact prefixLift 1319438
  have htrace : WordTrace (prefixWord ++ tailWord_1319438) baseStart_1319438 baseEnd_1319438 := by
    simpa [prefixWord, tailWord_1319438, baseEnd_1319438] using wordTrace_append hprefix tailTrace_1319438
  have hstable : (prefixWord ++ tailWord_1319438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319438).length < 2 ^ (prefixWord ++ tailWord_1319438).sum := by decide
  have hdescent : baseEnd_1319438 < baseStart_1319438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319461 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 8]
def baseStart_1319461 : Nat := 118140960795 + 1319461 * 2 ^ 59
def prefixEnd_1319461 : Nat := 4983230072969 + 3 ^ 40 * 1319461 * 2
def baseEnd_1319461 : Nat := 75279744206907481829935

theorem tailTrace_1319461 : CollatzResearch.WordTrace tailWord_1319461 prefixEnd_1319461 75279744206907481829935 := by
  unfold tailWord_1319461
  simp only [CollatzResearch.WordTrace]
  refine ⟨48124696272825617843198237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32083130848550411895465491 48124696272825617843198237)
  ·
    refine ⟨18046761102309606691199339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48124696272825617843198237 18046761102309606691199339)
    ·
      refine ⟨27070141653464410036799009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18046761102309606691199339 27070141653464410036799009)
      ·
        refine ⟨20302606240098307527599257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27070141653464410036799009 20302606240098307527599257)
        ·
          refine ⟨15226954680073730645699443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20302606240098307527599257 15226954680073730645699443)
          ·
            refine ⟨22840432020110595968549165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15226954680073730645699443 22840432020110595968549165)
            ·
              refine ⟨8565162007541473488205937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22840432020110595968549165 8565162007541473488205937)
              ·
                refine ⟨6423871505656105116154453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8565162007541473488205937 6423871505656105116154453)
                ·
                  refine ⟨75279744206907481829935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6423871505656105116154453 75279744206907481829935)
                  ·
                    rfl

theorem cell23_1319461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_1319461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319461 prefixEnd_1319461 := by exact prefixLift 1319461
  have htrace : WordTrace (prefixWord ++ tailWord_1319461) baseStart_1319461 baseEnd_1319461 := by
    simpa [prefixWord, tailWord_1319461, baseEnd_1319461] using wordTrace_append hprefix tailTrace_1319461
  have hstable : (prefixWord ++ tailWord_1319461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319461).length < 2 ^ (prefixWord ++ tailWord_1319461).sum := by decide
  have hdescent : baseEnd_1319461 < baseStart_1319461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319469 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1319469 : Nat := 118140960795 + 1319469 * 2 ^ 59
def prefixEnd_1319469 : Nat := 4983230072969 + 3 ^ 40 * 1319469 * 2
def baseEnd_1319469 : Nat := 225840601902467768389793

theorem tailTrace_1319469 : CollatzResearch.WordTrace tailWord_1319469 prefixEnd_1319469 225840601902467768389793 := by
  unfold tailWord_1319469
  simp only [CollatzResearch.WordTrace]
  refine ⟨48124988056796635209489461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32083325371197756806326307 48124988056796635209489461)
  ·
    refine ⟨4511717630324684550889637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48124988056796635209489461 4511717630324684550889637)
    ·
      refine ⟨845947055685878353291807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4511717630324684550889637 845947055685878353291807)
      ·
        refine ⟨1268920583528817529937711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845947055685878353291807 1268920583528817529937711)
        ·
          refine ⟨1903380875293226294906567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268920583528817529937711 1903380875293226294906567)
          ·
            refine ⟨2855071312939839442359851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903380875293226294906567 2855071312939839442359851)
            ·
              refine ⟨4282606969409759163539777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855071312939839442359851 4282606969409759163539777)
              ·
                refine ⟨3211955227057319372654833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282606969409759163539777 3211955227057319372654833)
                ·
                  refine ⟨2408966420292989529491125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3211955227057319372654833 2408966420292989529491125)
                  ·
                    refine ⟨225840601902467768389793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2408966420292989529491125 225840601902467768389793)
                    ·
                      rfl

theorem cell23_1319469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1319469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319469 prefixEnd_1319469 := by exact prefixLift 1319469
  have htrace : WordTrace (prefixWord ++ tailWord_1319469) baseStart_1319469 baseEnd_1319469 := by
    simpa [prefixWord, tailWord_1319469, baseEnd_1319469] using wordTrace_append hprefix tailTrace_1319469
  have hstable : (prefixWord ++ tailWord_1319469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319469).length < 2 ^ (prefixWord ++ tailWord_1319469).sum := by decide
  have hdescent : baseEnd_1319469 < baseStart_1319469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319495 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 6]
def baseStart_1319495 : Nat := 118140960795 + 1319495 * 2 ^ 59
def prefixEnd_1319495 : Nat := 4983230072969 + 3 ^ 40 * 1319495 * 2
def baseEnd_1319495 : Nat := 75281684022713355938251

theorem tailTrace_1319495 : CollatzResearch.WordTrace tailWord_1319495 prefixEnd_1319495 75281684022713355938251 := by
  unfold tailWord_1319495
  simp only [CollatzResearch.WordTrace]
  refine ⟨48125936354702441649935939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32083957569801627766623959 48125936354702441649935939)
  ·
    refine ⟨72188904532053662474903909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48125936354702441649935939 72188904532053662474903909)
    ·
      refine ⟨13535419599760061714044483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72188904532053662474903909 13535419599760061714044483)
      ·
        refine ⟨20303129399640092571066725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13535419599760061714044483 20303129399640092571066725)
        ·
          refine ⟨3806836762432517357075011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20303129399640092571066725 3806836762432517357075011)
          ·
            refine ⟨5710255143648776035612517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806836762432517357075011 5710255143648776035612517)
            ·
              refine ⟨1070672839434145506677347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5710255143648776035612517 1070672839434145506677347)
              ·
                refine ⟨1606009259151218260016021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070672839434145506677347 1606009259151218260016021)
                ·
                  refine ⟨75281684022713355938251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1606009259151218260016021 75281684022713355938251)
                  ·
                    rfl

theorem cell23_1319495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 6].length) (baseStart_1319495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319495 prefixEnd_1319495 := by exact prefixLift 1319495
  have htrace : WordTrace (prefixWord ++ tailWord_1319495) baseStart_1319495 baseEnd_1319495 := by
    simpa [prefixWord, tailWord_1319495, baseEnd_1319495] using wordTrace_append hprefix tailTrace_1319495
  have hstable : (prefixWord ++ tailWord_1319495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319495).length < 2 ^ (prefixWord ++ tailWord_1319495).sum := by decide
  have hdescent : baseEnd_1319495 < baseStart_1319495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319548 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_1319548 : Nat := 118140960795 + 1319548 * 2 ^ 59
def prefixEnd_1319548 : Nat := 4983230072969 + 3 ^ 40 * 1319548 * 2
def baseEnd_1319548 : Nat := 677562370679108496081515

theorem tailTrace_1319548 : CollatzResearch.WordTrace tailWord_1319548 prefixEnd_1319548 677562370679108496081515 := by
  unfold tailWord_1319548
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063934711755215850807649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32085246282340287801076865 24063934711755215850807649)
  ·
    refine ⟨18047951033816411888105737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24063934711755215850807649 18047951033816411888105737)
    ·
      refine ⟨13535963275362308916079303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18047951033816411888105737 13535963275362308916079303)
      ·
        refine ⟨20303944913043463374118955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13535963275362308916079303 20303944913043463374118955)
        ·
          refine ⟨30455917369565195061178433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20303944913043463374118955 30455917369565195061178433)
          ·
            refine ⟨22841938027173896295883825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30455917369565195061178433 22841938027173896295883825)
            ·
              refine ⟨17131453520380422221912869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22841938027173896295883825 17131453520380422221912869)
              ·
                refine ⟨3212147535071329166608663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17131453520380422221912869 3212147535071329166608663)
                ·
                  refine ⟨4818221302606993749912995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212147535071329166608663 4818221302606993749912995)
                  ·
                    refine ⟨7227331953910490624869493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4818221302606993749912995 7227331953910490624869493)
                    ·
                      refine ⟨677562370679108496081515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7227331953910490624869493 677562370679108496081515)
                      ·
                        rfl

theorem cell23_1319548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_1319548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319548 prefixEnd_1319548 := by exact prefixLift 1319548
  have htrace : WordTrace (prefixWord ++ tailWord_1319548) baseStart_1319548 baseEnd_1319548 := by
    simpa [prefixWord, tailWord_1319548, baseEnd_1319548] using wordTrace_append hprefix tailTrace_1319548
  have hstable : (prefixWord ++ tailWord_1319548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319548).length < 2 ^ (prefixWord ++ tailWord_1319548).sum := by decide
  have hdescent : baseEnd_1319548 < baseStart_1319548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319551 : List Nat := [1, 1, 2, 2, 1, 1, 1, 14]
def baseStart_1319551 : Nat := 118140960795 + 1319551 * 2 ^ 59
def prefixEnd_1319551 : Nat := 4983230072969 + 3 ^ 40 * 1319551 * 2
def baseEnd_1319551 : Nat := 25094959671150814234963

theorem tailTrace_1319551 : CollatzResearch.WordTrace tailWord_1319551 prefixEnd_1319551 25094959671150814234963 := by
  unfold tailWord_1319551
  simp only [CollatzResearch.WordTrace]
  refine ⟨48127978842499563213974507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32085319228333042142649671 48127978842499563213974507)
  ·
    refine ⟨72191968263749344820961761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48127978842499563213974507 72191968263749344820961761)
    ·
      refine ⟨54143976197812008615721321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72191968263749344820961761 54143976197812008615721321)
      ·
        refine ⟨40607982148359006461790991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54143976197812008615721321 40607982148359006461790991)
        ·
          refine ⟨60911973222538509692686487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40607982148359006461790991 60911973222538509692686487)
          ·
            refine ⟨91367959833807764539029731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60911973222538509692686487 91367959833807764539029731)
            ·
              refine ⟨137051939750711646808544597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91367959833807764539029731 137051939750711646808544597)
              ·
                refine ⟨25094959671150814234963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 137051939750711646808544597 25094959671150814234963)
                ·
                  rfl

theorem cell23_1319551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 14].length) (baseStart_1319551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319551 prefixEnd_1319551 := by exact prefixLift 1319551
  have htrace : WordTrace (prefixWord ++ tailWord_1319551) baseStart_1319551 baseEnd_1319551 := by
    simpa [prefixWord, tailWord_1319551, baseEnd_1319551] using wordTrace_append hprefix tailTrace_1319551
  have hstable : (prefixWord ++ tailWord_1319551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319551).length < 2 ^ (prefixWord ++ tailWord_1319551).sum := by decide
  have hdescent : baseEnd_1319551 < baseStart_1319551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319555 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 2, 4]
def baseStart_1319555 : Nat := 118140960795 + 1319555 * 2 ^ 59
def prefixEnd_1319555 : Nat := 4983230072969 + 3 ^ 40 * 1319555 * 2
def baseEnd_1319555 : Nat := 225855321681229989564661

theorem tailTrace_1319555 : CollatzResearch.WordTrace tailWord_1319555 prefixEnd_1319555 225855321681229989564661 := by
  unfold tailWord_1319555
  simp only [CollatzResearch.WordTrace]
  refine ⟨48128124734485071897120119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32085416489656714598080079 48128124734485071897120119)
  ·
    refine ⟨72192187101727607845680179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48128124734485071897120119 72192187101727607845680179)
    ·
      refine ⟨108288280652591411768520269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72192187101727607845680179 108288280652591411768520269)
      ·
        refine ⟨40608105244721779413195101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108288280652591411768520269 40608105244721779413195101)
        ·
          refine ⟨15228039466770667279948163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40608105244721779413195101 15228039466770667279948163)
          ·
            refine ⟨22842059200156000919922245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15228039466770667279948163 22842059200156000919922245)
            ·
              refine ⟨4282886100029250172485421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22842059200156000919922245 4282886100029250172485421)
              ·
                refine ⟨1606082287510968814682033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4282886100029250172485421 1606082287510968814682033)
                ·
                  refine ⟨1204561715633226611011525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606082287510968814682033 1204561715633226611011525)
                  ·
                    refine ⟨225855321681229989564661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1204561715633226611011525 225855321681229989564661)
                    ·
                      rfl

theorem cell23_1319555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 4].length) (baseStart_1319555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319555 prefixEnd_1319555 := by exact prefixLift 1319555
  have htrace : WordTrace (prefixWord ++ tailWord_1319555) baseStart_1319555 baseEnd_1319555 := by
    simpa [prefixWord, tailWord_1319555, baseEnd_1319555] using wordTrace_append hprefix tailTrace_1319555
  have hstable : (prefixWord ++ tailWord_1319555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319555).length < 2 ^ (prefixWord ++ tailWord_1319555).sum := by decide
  have hdescent : baseEnd_1319555 < baseStart_1319555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319606 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1319606 : Nat := 118140960795 + 1319606 * 2 ^ 59
def prefixEnd_1319606 : Nat := 4983230072969 + 3 ^ 40 * 1319606 * 2
def baseEnd_1319606 : Nat := 225864050852356423052083

theorem tailTrace_1319606 : CollatzResearch.WordTrace tailWord_1319606 prefixEnd_1319606 225864050852356423052083 := by
  unfold tailWord_1319606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008124053581269225451667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32086656571533538404817781 3008124053581269225451667)
  ·
    refine ⟨4512186080371903838177501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008124053581269225451667 4512186080371903838177501)
    ·
      refine ⟨1692069780139463939316563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4512186080371903838177501 1692069780139463939316563)
      ·
        refine ⟨2538104670209195908974845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692069780139463939316563 2538104670209195908974845)
        ·
          refine ⟨951789251328448465865567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2538104670209195908974845 951789251328448465865567)
          ·
            refine ⟨1427683876992672698798351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951789251328448465865567 1427683876992672698798351)
            ·
              refine ⟨2141525815489009048197527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427683876992672698798351 2141525815489009048197527)
              ·
                refine ⟨3212288723233513572296291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141525815489009048197527 3212288723233513572296291)
                ·
                  refine ⟨4818433084850270358444437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212288723233513572296291 4818433084850270358444437)
                  ·
                    refine ⟨225864050852356423052083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4818433084850270358444437 225864050852356423052083)
                    ·
                      rfl

theorem cell23_1319606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1319606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319606 prefixEnd_1319606 := by exact prefixLift 1319606
  have htrace : WordTrace (prefixWord ++ tailWord_1319606) baseStart_1319606 baseEnd_1319606 := by
    simpa [prefixWord, tailWord_1319606, baseEnd_1319606] using wordTrace_append hprefix tailTrace_1319606
  have hstable : (prefixWord ++ tailWord_1319606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319606).length < 2 ^ (prefixWord ++ tailWord_1319606).sum := by decide
  have hdescent : baseEnd_1319606 < baseStart_1319606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319712 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1319712 : Nat := 118140960795 + 1319712 * 2 ^ 59
def prefixEnd_1319712 : Nat := 4983230072969 + 3 ^ 40 * 1319712 * 2
def baseEnd_1319712 : Nat := 677646581506445854430761

theorem tailTrace_1319712 : CollatzResearch.WordTrace tailWord_1319712 prefixEnd_1319712 677646581506445854430761 := by
  unfold tailWord_1319712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24066925497458143855292695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32089233996610858473723593 24066925497458143855292695)
  ·
    refine ⟨36100388246187215782939043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24066925497458143855292695 36100388246187215782939043)
    ·
      refine ⟨54150582369280823674408565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36100388246187215782939043 54150582369280823674408565)
      ·
        refine ⟨5076617097120077219475803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54150582369280823674408565 5076617097120077219475803)
        ·
          refine ⟨7614925645680115829213705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5076617097120077219475803 7614925645680115829213705)
          ·
            refine ⟨5711194234260086871910279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7614925645680115829213705 5711194234260086871910279)
            ·
              refine ⟨8566791351390130307865419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711194234260086871910279 8566791351390130307865419)
              ·
                refine ⟨12850187027085195461798129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8566791351390130307865419 12850187027085195461798129)
                ·
                  refine ⟨9637640270313896596348597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12850187027085195461798129 9637640270313896596348597)
                  ·
                    refine ⟨903528775341927805907681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9637640270313896596348597 903528775341927805907681)
                    ·
                      refine ⟨677646581506445854430761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903528775341927805907681 677646581506445854430761)
                      ·
                        rfl

theorem cell23_1319712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1319712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319712 prefixEnd_1319712 := by exact prefixLift 1319712
  have htrace : WordTrace (prefixWord ++ tailWord_1319712) baseStart_1319712 baseEnd_1319712 := by
    simpa [prefixWord, tailWord_1319712, baseEnd_1319712] using wordTrace_append hprefix tailTrace_1319712
  have hstable : (prefixWord ++ tailWord_1319712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319712).length < 2 ^ (prefixWord ++ tailWord_1319712).sum := by decide
  have hdescent : baseEnd_1319712 < baseStart_1319712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319762 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1319762 : Nat := 118140960795 + 1319762 * 2 ^ 59
def prefixEnd_1319762 : Nat := 4983230072969 + 3 ^ 40 * 1319762 * 2
def baseEnd_1319762 : Nat := 677672255539170658805531

theorem tailTrace_1319762 : CollatzResearch.WordTrace tailWord_1319762 prefixEnd_1319762 677672255539170658805531 := by
  unfold tailWord_1319762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12033918661183786562476385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32090449763156764166603693 12033918661183786562476385)
  ·
    refine ⟨9025438995887839921857289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12033918661183786562476385 9025438995887839921857289)
    ·
      refine ⟨6769079246915879941392967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9025438995887839921857289 6769079246915879941392967)
      ·
        refine ⟨10153618870373819912089451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769079246915879941392967 10153618870373819912089451)
        ·
          refine ⟨15230428305560729868134177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10153618870373819912089451 15230428305560729868134177)
          ·
            refine ⟨11422821229170547401100633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15230428305560729868134177 11422821229170547401100633)
            ·
              refine ⟨8567115921877910550825475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11422821229170547401100633 8567115921877910550825475)
              ·
                refine ⟨12850673882816865826238213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567115921877910550825475 12850673882816865826238213)
                ·
                  refine ⟨2409501353028162342419665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12850673882816865826238213 2409501353028162342419665)
                  ·
                    refine ⟨1807126014771121756814749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2409501353028162342419665 1807126014771121756814749)
                    ·
                      refine ⟨677672255539170658805531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807126014771121756814749 677672255539170658805531)
                      ·
                        rfl

theorem cell23_1319762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1319762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319762 prefixEnd_1319762 := by exact prefixLift 1319762
  have htrace : WordTrace (prefixWord ++ tailWord_1319762) baseStart_1319762 baseEnd_1319762 := by
    simpa [prefixWord, tailWord_1319762, baseEnd_1319762] using wordTrace_append hprefix tailTrace_1319762
  have hstable : (prefixWord ++ tailWord_1319762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319762).length < 2 ^ (prefixWord ++ tailWord_1319762).sum := by decide
  have hdescent : baseEnd_1319762 < baseStart_1319762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319765 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 8]
def baseStart_1319765 : Nat := 118140960795 + 1319765 * 2 ^ 59
def prefixEnd_1319765 : Nat := 4983230072969 + 3 ^ 40 * 1319765 * 2
def baseEnd_1319765 : Nat := 75297088442348238563113

theorem tailTrace_1319765 : CollatzResearch.WordTrace tailWord_1319765 prefixEnd_1319765 75297088442348238563113 := by
  unfold tailWord_1319765
  simp only [CollatzResearch.WordTrace]
  refine ⟨48135784063724277762264749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32090522709149518508176499 48135784063724277762264749)
  ·
    refine ⟨18050919023896604160849281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48135784063724277762264749 18050919023896604160849281)
    ·
      refine ⟨13538189267922453120636961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18050919023896604160849281 13538189267922453120636961)
      ·
        refine ⟨10153641950941839840477721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13538189267922453120636961 10153641950941839840477721)
        ·
          refine ⟨7615231463206379880358291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10153641950941839840477721 7615231463206379880358291)
          ·
            refine ⟨11422847194809569820537437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615231463206379880358291 11422847194809569820537437)
            ·
              refine ⟨4283567698053588682701539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11422847194809569820537437 4283567698053588682701539)
              ·
                refine ⟨6425351547080383024052309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283567698053588682701539 6425351547080383024052309)
                ·
                  refine ⟨75297088442348238563113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6425351547080383024052309 75297088442348238563113)
                  ·
                    rfl

theorem cell23_1319765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_1319765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319765 prefixEnd_1319765 := by exact prefixLift 1319765
  have htrace : WordTrace (prefixWord ++ tailWord_1319765) baseStart_1319765 baseEnd_1319765 := by
    simpa [prefixWord, tailWord_1319765, baseEnd_1319765] using wordTrace_append hprefix tailTrace_1319765
  have hstable : (prefixWord ++ tailWord_1319765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319765).length < 2 ^ (prefixWord ++ tailWord_1319765).sum := by decide
  have hdescent : baseEnd_1319765 < baseStart_1319765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319769 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 1, 4]
def baseStart_1319769 : Nat := 118140960795 + 1319769 * 2 ^ 59
def prefixEnd_1319769 : Nat := 4983230072969 + 3 ^ 40 * 1319769 * 2
def baseEnd_1319769 : Nat := 225891949967917377139333

theorem tailTrace_1319769 : CollatzResearch.WordTrace tailWord_1319769 prefixEnd_1319769 225891949967917377139333 := by
  unfold tailWord_1319769
  simp only [CollatzResearch.WordTrace]
  refine ⟨48135929955709786445410361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32090619970473190963606907 48135929955709786445410361)
  ·
    refine ⟨36101947466782339834057771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48135929955709786445410361 36101947466782339834057771)
    ·
      refine ⟨54152921200173509751086657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36101947466782339834057771 54152921200173509751086657)
      ·
        refine ⟨40614690900130132313314993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54152921200173509751086657 40614690900130132313314993)
        ·
          refine ⟨30461018175097599234986245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40614690900130132313314993 30461018175097599234986245)
          ·
            refine ⟨5711440907830799856559921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30461018175097599234986245 5711440907830799856559921)
            ·
              refine ⟨4283580680873099892419941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5711440907830799856559921 4283580680873099892419941)
              ·
                refine ⟨803171377663706229828739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4283580680873099892419941 803171377663706229828739)
                ·
                  refine ⟨1204757066495559344743109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803171377663706229828739 1204757066495559344743109)
                  ·
                    refine ⟨225891949967917377139333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1204757066495559344743109 225891949967917377139333)
                    ·
                      rfl

theorem cell23_1319769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 4].length) (baseStart_1319769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319769 prefixEnd_1319769 := by exact prefixLift 1319769
  have htrace : WordTrace (prefixWord ++ tailWord_1319769) baseStart_1319769 baseEnd_1319769 := by
    simpa [prefixWord, tailWord_1319769, baseEnd_1319769] using wordTrace_append hprefix tailTrace_1319769
  have hstable : (prefixWord ++ tailWord_1319769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319769).length < 2 ^ (prefixWord ++ tailWord_1319769).sum := by decide
  have hdescent : baseEnd_1319769 < baseStart_1319769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319795 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 3, 5]
def baseStart_1319795 : Nat := 118140960795 + 1319795 * 2 ^ 59
def prefixEnd_1319795 : Nat := 4983230072969 + 3 ^ 40 * 1319795 * 2
def baseEnd_1319795 : Nat := 225896400133589676564293

theorem tailTrace_1319795 : CollatzResearch.WordTrace tailWord_1319795 prefixEnd_1319795 225896400133589676564293 := by
  unfold tailWord_1319795
  simp only [CollatzResearch.WordTrace]
  refine ⟨48136878253615592885856839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32091252169077061923904559 48136878253615592885856839)
  ·
    refine ⟨72205317380423389328785259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48136878253615592885856839 72205317380423389328785259)
    ·
      refine ⟨108307976070635083993177889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72205317380423389328785259 108307976070635083993177889)
      ·
        refine ⟨81230982052976312994883417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108307976070635083993177889 81230982052976312994883417)
        ·
          refine ⟨60923236539732234746162563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81230982052976312994883417 60923236539732234746162563)
          ·
            refine ⟨91384854809598352119243845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60923236539732234746162563 91384854809598352119243845)
            ·
              refine ⟨17134660276799691022358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91384854809598352119243845 17134660276799691022358221)
              ·
                refine ⟨6425497603799884133384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17134660276799691022358221 6425497603799884133384333)
                ·
                  refine ⟨2409561601424956550019125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6425497603799884133384333 2409561601424956550019125)
                  ·
                    refine ⟨225896400133589676564293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2409561601424956550019125 225896400133589676564293)
                    ·
                      rfl

theorem cell23_1319795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 5].length) (baseStart_1319795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319795 prefixEnd_1319795 := by exact prefixLift 1319795
  have htrace : WordTrace (prefixWord ++ tailWord_1319795) baseStart_1319795 baseEnd_1319795 := by
    simpa [prefixWord, tailWord_1319795, baseEnd_1319795] using wordTrace_append hprefix tailTrace_1319795
  have hstable : (prefixWord ++ tailWord_1319795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319795).length < 2 ^ (prefixWord ++ tailWord_1319795).sum := by decide
  have hdescent : baseEnd_1319795 < baseStart_1319795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319849 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 5, 2, 2]
def baseStart_1319849 : Nat := 118140960795 + 1319849 * 2 ^ 59
def prefixEnd_1319849 : Nat := 4983230072969 + 3 ^ 40 * 1319849 * 2
def baseEnd_1319849 : Nat := 677716928356111818417631

theorem tailTrace_1319849 : CollatzResearch.WordTrace tailWord_1319849 prefixEnd_1319849 677716928356111818417631 := by
  unfold tailWord_1319849
  simp only [CollatzResearch.WordTrace]
  refine ⟨48138847795419960108322601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32092565196946640072215067 48138847795419960108322601)
  ·
    refine ⟨36104135846564970081241951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48138847795419960108322601 36104135846564970081241951)
    ·
      refine ⟨54156203769847455121862927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36104135846564970081241951 54156203769847455121862927)
      ·
        refine ⟨81234305654771182682794391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54156203769847455121862927 81234305654771182682794391)
        ·
          refine ⟨121851458482156774024191587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81234305654771182682794391 121851458482156774024191587)
          ·
            refine ⟨182777187723235161036287381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121851458482156774024191587 182777187723235161036287381)
            ·
              refine ⟨8567680674526648173575971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182777187723235161036287381 8567680674526648173575971)
              ·
                refine ⟨12851521011789972260363957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567680674526648173575971 12851521011789972260363957)
                ·
                  refine ⟨1204830094855309899409121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12851521011789972260363957 1204830094855309899409121)
                  ·
                    refine ⟨903622571141482424556841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204830094855309899409121 903622571141482424556841)
                    ·
                      refine ⟨677716928356111818417631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903622571141482424556841 677716928356111818417631)
                      ·
                        rfl

theorem cell23_1319849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 2, 2].length) (baseStart_1319849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319849 prefixEnd_1319849 := by exact prefixLift 1319849
  have htrace : WordTrace (prefixWord ++ tailWord_1319849) baseStart_1319849 baseEnd_1319849 := by
    simpa [prefixWord, tailWord_1319849, baseEnd_1319849] using wordTrace_append hprefix tailTrace_1319849
  have hstable : (prefixWord ++ tailWord_1319849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319849).length < 2 ^ (prefixWord ++ tailWord_1319849).sum := by decide
  have hdescent : baseEnd_1319849 < baseStart_1319849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319852 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_1319852 : Nat := 118140960795 + 1319852 * 2 ^ 59
def prefixEnd_1319852 : Nat := 4983230072969 + 3 ^ 40 * 1319852 * 2
def baseEnd_1319852 : Nat := 677718468798075306680117

theorem tailTrace_1319852 : CollatzResearch.WordTrace tailWord_1319852 prefixEnd_1319852 677718468798075306680117 := by
  unfold tailWord_1319852
  simp only [CollatzResearch.WordTrace]
  refine ⟨24069478607204545810340905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32092638142939394413787873 24069478607204545810340905)
  ·
    refine ⟨18052108955403409357755679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24069478607204545810340905 18052108955403409357755679)
    ·
      refine ⟨27078163433105114036633519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18052108955403409357755679 27078163433105114036633519)
      ·
        refine ⟨40617245149657671054950279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27078163433105114036633519 40617245149657671054950279)
        ·
          refine ⟨60925867724486506582425419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40617245149657671054950279 60925867724486506582425419)
          ·
            refine ⟨91388801586729759873638129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60925867724486506582425419 91388801586729759873638129)
            ·
              refine ⟨68541601190047319905228597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91388801586729759873638129 68541601190047319905228597)
              ·
                refine ⟨6425775111566936241115181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68541601190047319905228597 6425775111566936241115181)
                ·
                  refine ⟨2409665666837601090418193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6425775111566936241115181 2409665666837601090418193)
                  ·
                    refine ⟨1807249250128200817813645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2409665666837601090418193 1807249250128200817813645)
                    ·
                      refine ⟨677718468798075306680117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807249250128200817813645 677718468798075306680117)
                      ·
                        rfl

theorem cell23_1319852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_1319852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319852 prefixEnd_1319852 := by exact prefixLift 1319852
  have htrace : WordTrace (prefixWord ++ tailWord_1319852) baseStart_1319852 baseEnd_1319852 := by
    simpa [prefixWord, tailWord_1319852, baseEnd_1319852] using wordTrace_append hprefix tailTrace_1319852
  have hstable : (prefixWord ++ tailWord_1319852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319852).length < 2 ^ (prefixWord ++ tailWord_1319852).sum := by decide
  have hdescent : baseEnd_1319852 < baseStart_1319852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319882 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1319882 : Nat := 118140960795 + 1319882 * 2 ^ 59
def prefixEnd_1319882 : Nat := 4983230072969 + 3 ^ 40 * 1319882 * 2
def baseEnd_1319882 : Nat := 677733873217710189304979

theorem tailTrace_1319882 : CollatzResearch.WordTrace tailWord_1319882 prefixEnd_1319882 677733873217710189304979 := by
  unfold tailWord_1319882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035012851075101686068475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32093367602866937829515933 12035012851075101686068475)
  ·
    refine ⟨18052519276612652529102713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12035012851075101686068475 18052519276612652529102713)
    ·
      refine ⟨13539389457459489396827035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18052519276612652529102713 13539389457459489396827035)
      ·
        refine ⟨20309084186189234095240553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13539389457459489396827035 20309084186189234095240553)
        ·
          refine ⟨15231813139641925571430415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20309084186189234095240553 15231813139641925571430415)
          ·
            refine ⟨22847719709462888357145623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15231813139641925571430415 22847719709462888357145623)
            ·
              refine ⟨34271579564194332535718435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22847719709462888357145623 34271579564194332535718435)
              ·
                refine ⟨51407369346291498803577653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34271579564194332535718435 51407369346291498803577653)
                ·
                  refine ⟨4819440876214828012835405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51407369346291498803577653 4819440876214828012835405)
                  ·
                    refine ⟨1807290328580560504813277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4819440876214828012835405 1807290328580560504813277)
                    ·
                      refine ⟨677733873217710189304979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807290328580560504813277 677733873217710189304979)
                      ·
                        rfl

theorem cell23_1319882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1319882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319882 prefixEnd_1319882 := by exact prefixLift 1319882
  have htrace : WordTrace (prefixWord ++ tailWord_1319882) baseStart_1319882 baseEnd_1319882 := by
    simpa [prefixWord, tailWord_1319882, baseEnd_1319882] using wordTrace_append hprefix tailTrace_1319882
  have hstable : (prefixWord ++ tailWord_1319882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319882).length < 2 ^ (prefixWord ++ tailWord_1319882).sum := by decide
  have hdescent : baseEnd_1319882 < baseStart_1319882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319883 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 1, 2, 2]
def baseStart_1319883 : Nat := 118140960795 + 1319883 * 2 ^ 59
def prefixEnd_1319883 : Nat := 4983230072969 + 3 ^ 40 * 1319883 * 2
def baseEnd_1319883 : Nat := 677734386698364685392475

theorem tailTrace_1319883 : CollatzResearch.WordTrace tailWord_1319883 prefixEnd_1319883 677734386698364685392475 := by
  unfold tailWord_1319883
  simp only [CollatzResearch.WordTrace]
  refine ⟨48140087877296783915060303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32093391918197855943373535 48140087877296783915060303)
  ·
    refine ⟨72210131815945175872590455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48140087877296783915060303 72210131815945175872590455)
    ·
      refine ⟨108315197723917763808885683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72210131815945175872590455 108315197723917763808885683)
      ·
        refine ⟨162472796585876645713328525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108315197723917763808885683 162472796585876645713328525)
        ·
          refine ⟨60927298719703742142498197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162472796585876645713328525 60927298719703742142498197)
          ·
            refine ⟨2855967127486112912929603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60927298719703742142498197 2855967127486112912929603)
            ·
              refine ⟨4283950691229169369394405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855967127486112912929603 4283950691229169369394405)
              ·
                refine ⟨803240754605469256761451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4283950691229169369394405 803240754605469256761451)
                ·
                  refine ⟨1204861131908203885142177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803240754605469256761451 1204861131908203885142177)
                  ·
                    refine ⟨903645848931152913856633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204861131908203885142177 903645848931152913856633)
                    ·
                      refine ⟨677734386698364685392475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903645848931152913856633 677734386698364685392475)
                      ·
                        rfl

theorem cell23_1319883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 2, 2].length) (baseStart_1319883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319883 prefixEnd_1319883 := by exact prefixLift 1319883
  have htrace : WordTrace (prefixWord ++ tailWord_1319883) baseStart_1319883 baseEnd_1319883 := by
    simpa [prefixWord, tailWord_1319883, baseEnd_1319883] using wordTrace_append hprefix tailTrace_1319883
  have hstable : (prefixWord ++ tailWord_1319883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319883).length < 2 ^ (prefixWord ++ tailWord_1319883).sum := by decide
  have hdescent : baseEnd_1319883 < baseStart_1319883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319906 : List Nat := [3, 3, 3, 1, 1, 2, 3, 7]
def baseStart_1319906 : Nat := 118140960795 + 1319906 * 2 ^ 59
def prefixEnd_1319906 : Nat := 4983230072969 + 3 ^ 40 * 1319906 * 2
def baseEnd_1319906 : Nat := 25101710990867336866847

theorem tailTrace_1319906 : CollatzResearch.WordTrace tailWord_1319906 prefixEnd_1319906 25101710990867336866847 := by
  unfold tailWord_1319906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035231689053364710786893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32093951170808972562098381 12035231689053364710786893)
  ·
    refine ⟨4513211883395011766545085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12035231689053364710786893 4513211883395011766545085)
    ·
      refine ⟨1692454456273129412454407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4513211883395011766545085 1692454456273129412454407)
      ·
        refine ⟨2538681684409694118681611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692454456273129412454407 2538681684409694118681611)
        ·
          refine ⟨3808022526614541178022417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538681684409694118681611 3808022526614541178022417)
          ·
            refine ⟨2856016894960905883516813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808022526614541178022417 2856016894960905883516813)
            ·
              refine ⟨1071006335610339706318805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2856016894960905883516813 1071006335610339706318805)
              ·
                refine ⟨25101710990867336866847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1071006335610339706318805 25101710990867336866847)
                ·
                  rfl

theorem cell23_1319906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_1319906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319906 prefixEnd_1319906 := by exact prefixLift 1319906
  have htrace : WordTrace (prefixWord ++ tailWord_1319906) baseStart_1319906 baseEnd_1319906 := by
    simpa [prefixWord, tailWord_1319906, baseEnd_1319906] using wordTrace_append hprefix tailTrace_1319906
  have hstable : (prefixWord ++ tailWord_1319906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319906).length < 2 ^ (prefixWord ++ tailWord_1319906).sum := by decide
  have hdescent : baseEnd_1319906 < baseStart_1319906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319932 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1319932 : Nat := 118140960795 + 1319932 * 2 ^ 59
def prefixEnd_1319932 : Nat := 4983230072969 + 3 ^ 40 * 1319932 * 2
def baseEnd_1319932 : Nat := 225919849083478331226583

theorem tailTrace_1319932 : CollatzResearch.WordTrace tailWord_1319932 prefixEnd_1319932 225919849083478331226583 := by
  unfold tailWord_1319932
  simp only [CollatzResearch.WordTrace]
  refine ⟨24070937527059632641797025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32094583369412843522396033 24070937527059632641797025)
  ·
    refine ⟨18053203145294724481347769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24070937527059632641797025 18053203145294724481347769)
    ·
      refine ⟨13539902358971043361010827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18053203145294724481347769 13539902358971043361010827)
      ·
        refine ⟨20309853538456565041516241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13539902358971043361010827 20309853538456565041516241)
        ·
          refine ⟨15232390153842423781137181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20309853538456565041516241 15232390153842423781137181)
          ·
            refine ⟨5712146307690908917926443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15232390153842423781137181 5712146307690908917926443)
            ·
              refine ⟨8568219461536363376889665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712146307690908917926443 8568219461536363376889665)
              ·
                refine ⟨6426164596152272532667249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8568219461536363376889665 6426164596152272532667249)
                ·
                  refine ⟨4819623447114204399500437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6426164596152272532667249 4819623447114204399500437)
                  ·
                    refine ⟨225919849083478331226583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4819623447114204399500437 225919849083478331226583)
                    ·
                      rfl

theorem cell23_1319932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1319932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319932 prefixEnd_1319932 := by exact prefixLift 1319932
  have htrace : WordTrace (prefixWord ++ tailWord_1319932) baseStart_1319932 baseEnd_1319932 := by
    simpa [prefixWord, tailWord_1319932, baseEnd_1319932] using wordTrace_append hprefix tailTrace_1319932
  have hstable : (prefixWord ++ tailWord_1319932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319932).length < 2 ^ (prefixWord ++ tailWord_1319932).sum := by decide
  have hdescent : baseEnd_1319932 < baseStart_1319932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319962 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_1319962 : Nat := 118140960795 + 1319962 * 2 ^ 59
def prefixEnd_1319962 : Nat := 4983230072969 + 3 ^ 40 * 1319962 * 2
def baseEnd_1319962 : Nat := 75308327963341097367179

theorem tailTrace_1319962 : CollatzResearch.WordTrace tailWord_1319962 prefixEnd_1319962 75308327963341097367179 := by
  unfold tailWord_1319962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035742311002645101796535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32095312829340386938124093 12035742311002645101796535)
  ·
    refine ⟨18053613466503967652694803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12035742311002645101796535 18053613466503967652694803)
    ·
      refine ⟨27080420199755951479042205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18053613466503967652694803 27080420199755951479042205)
      ·
        refine ⟨10155157574908481804640827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27080420199755951479042205 10155157574908481804640827)
        ·
          refine ⟨15232736362362722706961241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10155157574908481804640827 15232736362362722706961241)
          ·
            refine ⟨11424552271772042030220931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15232736362362722706961241 11424552271772042030220931)
            ·
              refine ⟨17136828407658063045331397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11424552271772042030220931 17136828407658063045331397)
              ·
                refine ⟨3213155326435886820999637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17136828407658063045331397 3213155326435886820999637)
                ·
                  refine ⟨75308327963341097367179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3213155326435886820999637 75308327963341097367179)
                  ·
                    rfl

theorem cell23_1319962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_1319962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319962 prefixEnd_1319962 := by exact prefixLift 1319962
  have htrace : WordTrace (prefixWord ++ tailWord_1319962) baseStart_1319962 baseEnd_1319962 := by
    simpa [prefixWord, tailWord_1319962, baseEnd_1319962] using wordTrace_append hprefix tailTrace_1319962
  have hstable : (prefixWord ++ tailWord_1319962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319962).length < 2 ^ (prefixWord ++ tailWord_1319962).sum := by decide
  have hdescent : baseEnd_1319962 < baseStart_1319962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319999 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 2, 5, 2]
def baseStart_1319999 : Nat := 118140960795 + 1319999 * 2 ^ 59
def prefixEnd_1319999 : Nat := 4983230072969 + 3 ^ 40 * 1319999 * 2
def baseEnd_1319999 : Nat := 677793950454286231541941

theorem tailTrace_1319999 : CollatzResearch.WordTrace tailWord_1319999 prefixEnd_1319999 677793950454286231541941 := by
  unfold tailWord_1319999
  simp only [CollatzResearch.WordTrace]
  refine ⟨48144318744876535726283051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32096212496584357150855367 48144318744876535726283051)
  ·
    refine ⟨72216478117314803589424577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48144318744876535726283051 72216478117314803589424577)
    ·
      refine ⟨54162358587986102692068433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72216478117314803589424577 54162358587986102692068433)
      ·
        refine ⟨40621768940989577019051325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54162358587986102692068433 40621768940989577019051325)
        ·
          refine ⟨15233163352871091382144247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40621768940989577019051325 15233163352871091382144247)
          ·
            refine ⟨22849745029306637073216371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15233163352871091382144247 22849745029306637073216371)
            ·
              refine ⟨34274617543959955609824557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22849745029306637073216371 34274617543959955609824557)
              ·
                refine ⟨12852981578984983353684209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34274617543959955609824557 12852981578984983353684209)
                ·
                  refine ⟨9639736184238737515263157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12852981578984983353684209 9639736184238737515263157)
                  ·
                    refine ⟨903725267272381642055921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9639736184238737515263157 903725267272381642055921)
                    ·
                      refine ⟨677793950454286231541941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903725267272381642055921 677793950454286231541941)
                      ·
                        rfl

theorem cell23_1319999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_1319999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1319999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1319999 prefixEnd_1319999 := by exact prefixLift 1319999
  have htrace : WordTrace (prefixWord ++ tailWord_1319999) baseStart_1319999 baseEnd_1319999 := by
    simpa [prefixWord, tailWord_1319999, baseEnd_1319999] using wordTrace_append hprefix tailTrace_1319999
  have hstable : (prefixWord ++ tailWord_1319999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319999).length < 2 ^ (prefixWord ++ tailWord_1319999).sum := by decide
  have hdescent : baseEnd_1319999 < baseStart_1319999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320046 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1320046 : Nat := 118140960795 + 1320046 * 2 ^ 59
def prefixEnd_1320046 : Nat := 4983230072969 + 3 ^ 40 * 1320046 * 2
def baseEnd_1320046 : Nat := 677818084045047547654225

theorem tailTrace_1320046 : CollatzResearch.WordTrace tailWord_1320046 prefixEnd_1320046 677818084045047547654225 := by
  unfold tailWord_1320046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6018254121963282844155499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32097355317137508502162661 6018254121963282844155499)
  ·
    refine ⟨9027381182944924266233249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6018254121963282844155499 9027381182944924266233249)
    ·
      refine ⟨6770535887208693199674937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9027381182944924266233249 6770535887208693199674937)
      ·
        refine ⟨5077901915406519899756203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6770535887208693199674937 5077901915406519899756203)
        ·
          refine ⟨7616852873109779849634305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077901915406519899756203 7616852873109779849634305)
          ·
            refine ⟨5712639654832334887225729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616852873109779849634305 5712639654832334887225729)
            ·
              refine ⟨4284479741124251165419297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5712639654832334887225729 4284479741124251165419297)
              ·
                refine ⟨3213359805843188374064473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4284479741124251165419297 3213359805843188374064473)
                ·
                  refine ⟨2410019854382391280548355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3213359805843188374064473 2410019854382391280548355)
                  ·
                    refine ⟨3615029781573586920822533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2410019854382391280548355 3615029781573586920822533)
                    ·
                      refine ⟨677818084045047547654225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3615029781573586920822533 677818084045047547654225)
                      ·
                        rfl

theorem cell23_1320046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1320046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320046 prefixEnd_1320046 := by exact prefixLift 1320046
  have htrace : WordTrace (prefixWord ++ tailWord_1320046) baseStart_1320046 baseEnd_1320046 := by
    simpa [prefixWord, tailWord_1320046, baseEnd_1320046] using wordTrace_append hprefix tailTrace_1320046
  have hstable : (prefixWord ++ tailWord_1320046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320046).length < 2 ^ (prefixWord ++ tailWord_1320046).sum := by decide
  have hdescent : baseEnd_1320046 < baseStart_1320046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320049 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_1320049 : Nat := 118140960795 + 1320049 * 2 ^ 59
def prefixEnd_1320049 : Nat := 4983230072969 + 3 ^ 40 * 1320049 * 2
def baseEnd_1320049 : Nat := 677819624487011035916711

theorem tailTrace_1320049 : CollatzResearch.WordTrace tailWord_1320049 prefixEnd_1320049 677819624487011035916711 := by
  unfold tailWord_1320049
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146142394695394265603201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32097428263130262843735467 48146142394695394265603201)
  ·
    refine ⟨36109606796021545699202401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48146142394695394265603201 36109606796021545699202401)
    ·
      refine ⟨27082205097016159274401801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36109606796021545699202401 27082205097016159274401801)
      ·
        refine ⟨20311653822762119455801351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27082205097016159274401801 20311653822762119455801351)
        ·
          refine ⟨30467480734143179183702027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20311653822762119455801351 30467480734143179183702027)
          ·
            refine ⟨45701221101214768775553041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30467480734143179183702027 45701221101214768775553041)
            ·
              refine ⟨34275915825911076581664781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45701221101214768775553041 34275915825911076581664781)
              ·
                refine ⟨12853468434716653718124293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34275915825911076581664781 12853468434716653718124293)
                ·
                  refine ⟨2410025331509372572148305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12853468434716653718124293 2410025331509372572148305)
                  ·
                    refine ⟨1807518998632029429111229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2410025331509372572148305 1807518998632029429111229)
                    ·
                      refine ⟨677819624487011035916711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807518998632029429111229 677819624487011035916711)
                      ·
                        rfl

theorem cell23_1320049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_1320049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320049 prefixEnd_1320049 := by exact prefixLift 1320049
  have htrace : WordTrace (prefixWord ++ tailWord_1320049) baseStart_1320049 baseEnd_1320049 := by
    simpa [prefixWord, tailWord_1320049, baseEnd_1320049] using wordTrace_append hprefix tailTrace_1320049
  have hstable : (prefixWord ++ tailWord_1320049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320049).length < 2 ^ (prefixWord ++ tailWord_1320049).sum := by decide
  have hdescent : baseEnd_1320049 < baseStart_1320049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320090 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_1320090 : Nat := 118140960795 + 1320090 * 2 ^ 59
def prefixEnd_1320090 : Nat := 4983230072969 + 3 ^ 40 * 1320090 * 2
def baseEnd_1320090 : Nat := 225946892397948458501341

theorem tailTrace_1320090 : CollatzResearch.WordTrace tailWord_1320090 prefixEnd_1320090 225946892397948458501341 := by
  unfold tailWord_1320090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12036909446886714566961431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32098425191697905511897149 12036909446886714566961431)
  ·
    refine ⟨18055364170330071850442147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12036909446886714566961431 18055364170330071850442147)
    ·
      refine ⟨27083046255495107775663221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18055364170330071850442147 27083046255495107775663221)
      ·
        refine ⟨2539035586452666353968427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27083046255495107775663221 2539035586452666353968427)
        ·
          refine ⟨3808553379678999530952641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539035586452666353968427 3808553379678999530952641)
          ·
            refine ⟨2856415034759249648214481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808553379678999530952641 2856415034759249648214481)
            ·
              refine ⟨2142311276069437236160861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856415034759249648214481 2142311276069437236160861)
              ·
                refine ⟨803366728526038963560323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2142311276069437236160861 803366728526038963560323)
                ·
                  refine ⟨1205050092789058445340485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803366728526038963560323 1205050092789058445340485)
                  ·
                    refine ⟨225946892397948458501341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205050092789058445340485 225946892397948458501341)
                    ·
                      rfl

theorem cell23_1320090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_1320090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320090 prefixEnd_1320090 := by exact prefixLift 1320090
  have htrace : WordTrace (prefixWord ++ tailWord_1320090) baseStart_1320090 baseEnd_1320090 := by
    simpa [prefixWord, tailWord_1320090, baseEnd_1320090] using wordTrace_append hprefix tailTrace_1320090
  have hstable : (prefixWord ++ tailWord_1320090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320090).length < 2 ^ (prefixWord ++ tailWord_1320090).sum := by decide
  have hdescent : baseEnd_1320090 < baseStart_1320090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320096 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1320096 : Nat := 118140960795 + 1320096 * 2 ^ 59
def prefixEnd_1320096 : Nat := 4983230072969 + 3 ^ 40 * 1320096 * 2
def baseEnd_1320096 : Nat := 677843758077772352028995

theorem tailTrace_1320096 : CollatzResearch.WordTrace tailWord_1320096 prefixEnd_1320096 677843758077772352028995 := by
  unfold tailWord_1320096
  simp only [CollatzResearch.WordTrace]
  refine ⟨24073928312762560646282071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32098571083683414195042761 24073928312762560646282071)
  ·
    refine ⟨36110892469143840969423107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24073928312762560646282071 36110892469143840969423107)
    ·
      refine ⟨54166338703715761454134661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36110892469143840969423107 54166338703715761454134661)
      ·
        refine ⟨10156188506946705272650249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54166338703715761454134661 10156188506946705272650249)
        ·
          refine ⟨7617141380210028954487687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10156188506946705272650249 7617141380210028954487687)
          ·
            refine ⟨11425712070315043431731531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7617141380210028954487687 11425712070315043431731531)
            ·
              refine ⟨17138568105472565147597297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11425712070315043431731531 17138568105472565147597297)
              ·
                refine ⟨12853926079104423860697973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17138568105472565147597297 12853926079104423860697973)
                ·
                  refine ⟨1205055569916039736940435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12853926079104423860697973 1205055569916039736940435)
                  ·
                    refine ⟨1807583354874059605410653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205055569916039736940435 1807583354874059605410653)
                    ·
                      refine ⟨677843758077772352028995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807583354874059605410653 677843758077772352028995)
                      ·
                        rfl

theorem cell23_1320096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1320096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320096 prefixEnd_1320096 := by exact prefixLift 1320096
  have htrace : WordTrace (prefixWord ++ tailWord_1320096) baseStart_1320096 baseEnd_1320096 := by
    simpa [prefixWord, tailWord_1320096, baseEnd_1320096] using wordTrace_append hprefix tailTrace_1320096
  have hstable : (prefixWord ++ tailWord_1320096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320096).length < 2 ^ (prefixWord ++ tailWord_1320096).sum := by decide
  have hdescent : baseEnd_1320096 < baseStart_1320096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320103 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 6]
def baseStart_1320103 : Nat := 118140960795 + 1320103 * 2 ^ 59
def prefixEnd_1320103 : Nat := 4983230072969 + 3 ^ 40 * 1320103 * 2
def baseEnd_1320103 : Nat := 75316372493594869404607

theorem tailTrace_1320103 : CollatzResearch.WordTrace tailWord_1320103 prefixEnd_1320103 75316372493594869404607 := by
  unfold tailWord_1320103
  simp only [CollatzResearch.WordTrace]
  refine ⟨48148111936499761488068963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32098741290999840992045975 48148111936499761488068963)
  ·
    refine ⟨72222167904749642232103445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48148111936499761488068963 72222167904749642232103445)
    ·
      refine ⟨3385414120535139479629849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72222167904749642232103445 3385414120535139479629849)
      ·
        refine ⟨2539060590401354609722387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3385414120535139479629849 2539060590401354609722387)
        ·
          refine ⟨3808590885602031914583581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539060590401354609722387 3808590885602031914583581)
          ·
            refine ⟨1428221582100761967968843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3808590885602031914583581 1428221582100761967968843)
            ·
              refine ⟨2142332373151142951953265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428221582100761967968843 2142332373151142951953265)
              ·
                refine ⟨1606749279863357213964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142332373151142951953265 1606749279863357213964949)
                ·
                  refine ⟨75316372493594869404607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1606749279863357213964949 75316372493594869404607)
                  ·
                    rfl

theorem cell23_1320103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 6].length) (baseStart_1320103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320103 prefixEnd_1320103 := by exact prefixLift 1320103
  have htrace : WordTrace (prefixWord ++ tailWord_1320103) baseStart_1320103 baseEnd_1320103 := by
    simpa [prefixWord, tailWord_1320103, baseEnd_1320103] using wordTrace_append hprefix tailTrace_1320103
  have hstable : (prefixWord ++ tailWord_1320103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320103).length < 2 ^ (prefixWord ++ tailWord_1320103).sum := by decide
  have hdescent : baseEnd_1320103 < baseStart_1320103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320106 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1320106 : Nat := 118140960795 + 1320106 * 2 ^ 59
def prefixEnd_1320106 : Nat := 4983230072969 + 3 ^ 40 * 1320106 * 2
def baseEnd_1320106 : Nat := 677848892884317312903949

theorem tailTrace_1320106 : CollatzResearch.WordTrace tailWord_1320106 prefixEnd_1320106 677848892884317312903949 := by
  unfold tailWord_1320106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037055338872223250107043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32098814236992595333618781 12037055338872223250107043)
  ·
    refine ⟨18055583008308334875160565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12037055338872223250107043 18055583008308334875160565)
    ·
      refine ⟨1692710907028906394546303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18055583008308334875160565 1692710907028906394546303)
      ·
        refine ⟨2539066360543359591819455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692710907028906394546303 2539066360543359591819455)
        ·
          refine ⟨3808599540815039387729183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539066360543359591819455 3808599540815039387729183)
          ·
            refine ⟨5712899311222559081593775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808599540815039387729183 5712899311222559081593775)
            ·
              refine ⟨8569348966833838622390663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712899311222559081593775 8569348966833838622390663)
              ·
                refine ⟨12854023450250757933585995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8569348966833838622390663 12854023450250757933585995)
                ·
                  refine ⟨19281035175376136900378993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12854023450250757933585995 19281035175376136900378993)
                  ·
                    refine ⟨14460776381532102675284245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19281035175376136900378993 14460776381532102675284245)
                    ·
                      refine ⟨677848892884317312903949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14460776381532102675284245 677848892884317312903949)
                      ·
                        rfl

theorem cell23_1320106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1320106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320106 prefixEnd_1320106 := by exact prefixLift 1320106
  have htrace : WordTrace (prefixWord ++ tailWord_1320106) baseStart_1320106 baseEnd_1320106 := by
    simpa [prefixWord, tailWord_1320106, baseEnd_1320106] using wordTrace_append hprefix tailTrace_1320106
  have hstable : (prefixWord ++ tailWord_1320106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320106).length < 2 ^ (prefixWord ++ tailWord_1320106).sum := by decide
  have hdescent : baseEnd_1320106 < baseStart_1320106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320113 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1320113 : Nat := 118140960795 + 1320113 * 2 ^ 59
def prefixEnd_1320113 : Nat := 4983230072969 + 3 ^ 40 * 1320113 * 2
def baseEnd_1320113 : Nat := 677852487248898785516417

theorem tailTrace_1320113 : CollatzResearch.WordTrace tailWord_1320113 prefixEnd_1320113 677852487248898785516417 := by
  unfold tailWord_1320113
  simp only [CollatzResearch.WordTrace]
  refine ⟨48148476666463533195932993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32098984444309022130621995 48148476666463533195932993)
  ·
    refine ⟨36111357499847649896949745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48148476666463533195932993 36111357499847649896949745)
    ·
      refine ⟨27083518124885737422712309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36111357499847649896949745 27083518124885737422712309)
      ·
        refine ⟨2539079824208037883379279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27083518124885737422712309 2539079824208037883379279)
        ·
          refine ⟨3808619736312056825068919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539079824208037883379279 3808619736312056825068919)
          ·
            refine ⟨5712929604468085237603379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808619736312056825068919 5712929604468085237603379)
            ·
              refine ⟨8569394406702127856405069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712929604468085237603379 8569394406702127856405069)
              ·
                refine ⟨3213522902513297946151901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8569394406702127856405069 3213522902513297946151901)
                ·
                  refine ⟨1205071088442486729806963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3213522902513297946151901 1205071088442486729806963)
                  ·
                    refine ⟨1807606632663730094710445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205071088442486729806963 1807606632663730094710445)
                    ·
                      refine ⟨677852487248898785516417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807606632663730094710445 677852487248898785516417)
                      ·
                        rfl

theorem cell23_1320113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1320113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320113 prefixEnd_1320113 := by exact prefixLift 1320113
  have htrace : WordTrace (prefixWord ++ tailWord_1320113) baseStart_1320113 baseEnd_1320113 := by
    simpa [prefixWord, tailWord_1320113, baseEnd_1320113] using wordTrace_append hprefix tailTrace_1320113
  have hstable : (prefixWord ++ tailWord_1320113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320113).length < 2 ^ (prefixWord ++ tailWord_1320113).sum := by decide
  have hdescent : baseEnd_1320113 < baseStart_1320113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320136 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_1320136 : Nat := 118140960795 + 1320136 * 2 ^ 59
def prefixEnd_1320136 : Nat := 4983230072969 + 3 ^ 40 * 1320136 * 2
def baseEnd_1320136 : Nat := 677864297303952195528811

theorem tailTrace_1320136 : CollatzResearch.WordTrace tailWord_1320136 prefixEnd_1320136 677864297303952195528811 := by
  unfold tailWord_1320136
  simp only [CollatzResearch.WordTrace]
  refine ⟨24074657772690104062010131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32099543696920138749346841 24074657772690104062010131)
  ·
    refine ⟨36111986659035156093015197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24074657772690104062010131 36111986659035156093015197)
    ·
      refine ⟨13541994997138183534880699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36111986659035156093015197 13541994997138183534880699)
      ·
        refine ⟨20312992495707275302321049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13541994997138183534880699 20312992495707275302321049)
        ·
          refine ⟨15234744371780456476740787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20312992495707275302321049 15234744371780456476740787)
          ·
            refine ⟨22852116557670684715111181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15234744371780456476740787 22852116557670684715111181)
            ·
              refine ⟨8569543709126506768166693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22852116557670684715111181 8569543709126506768166693)
              ·
                refine ⟨1606789445461220019031255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8569543709126506768166693 1606789445461220019031255)
                ·
                  refine ⟨2410184168191830028546883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606789445461220019031255 2410184168191830028546883)
                  ·
                    refine ⟨3615276252287745042820325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2410184168191830028546883 3615276252287745042820325)
                    ·
                      refine ⟨677864297303952195528811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3615276252287745042820325 677864297303952195528811)
                      ·
                        rfl

theorem cell23_1320136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_1320136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320136 prefixEnd_1320136 := by exact prefixLift 1320136
  have htrace : WordTrace (prefixWord ++ tailWord_1320136) baseStart_1320136 baseEnd_1320136 := by
    simpa [prefixWord, tailWord_1320136, baseEnd_1320136] using wordTrace_append hprefix tailTrace_1320136
  have hstable : (prefixWord ++ tailWord_1320136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320136).length < 2 ^ (prefixWord ++ tailWord_1320136).sum := by decide
  have hdescent : baseEnd_1320136 < baseStart_1320136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320141 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1320141 : Nat := 118140960795 + 1320141 * 2 ^ 59
def prefixEnd_1320141 : Nat := 4983230072969 + 3 ^ 40 * 1320141 * 2
def baseEnd_1320141 : Nat := 225955621569074891988763

theorem tailTrace_1320141 : CollatzResearch.WordTrace tailWord_1320141 prefixEnd_1320141 225955621569074891988763 := by
  unfold tailWord_1320141
  simp only [CollatzResearch.WordTrace]
  refine ⟨48149497910362093977952277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32099665273574729318634851 48149497910362093977952277)
  ·
    refine ⟨2257007714548223155216513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48149497910362093977952277 2257007714548223155216513)
    ·
      refine ⟨1692755785911167366412385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2257007714548223155216513 1692755785911167366412385)
      ·
        refine ⟨1269566839433375524809289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1692755785911167366412385 1269566839433375524809289)
        ·
          refine ⟨952175129575031643606967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1269566839433375524809289 952175129575031643606967)
          ·
            refine ⟨1428262694362547465410451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952175129575031643606967 1428262694362547465410451)
            ·
              refine ⟨2142394041543821198115677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428262694362547465410451 2142394041543821198115677)
              ·
                refine ⟨803397765578932949293379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2142394041543821198115677 803397765578932949293379)
                ·
                  refine ⟨1205096648368399423940069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803397765578932949293379 1205096648368399423940069)
                  ·
                    refine ⟨225955621569074891988763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205096648368399423940069 225955621569074891988763)
                    ·
                      rfl

theorem cell23_1320141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1320141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320141 prefixEnd_1320141 := by exact prefixLift 1320141
  have htrace : WordTrace (prefixWord ++ tailWord_1320141) baseStart_1320141 baseEnd_1320141 := by
    simpa [prefixWord, tailWord_1320141, baseEnd_1320141] using wordTrace_append hprefix tailTrace_1320141
  have hstable : (prefixWord ++ tailWord_1320141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320141).length < 2 ^ (prefixWord ++ tailWord_1320141).sum := by decide
  have hdescent : baseEnd_1320141 < baseStart_1320141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320146 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1320146 : Nat := 118140960795 + 1320146 * 2 ^ 59
def prefixEnd_1320146 : Nat := 4983230072969 + 3 ^ 40 * 1320146 * 2
def baseEnd_1320146 : Nat := 225956477370165718801255

theorem tailTrace_1320146 : CollatzResearch.WordTrace tailWord_1320146 prefixEnd_1320146 225956477370165718801255 := by
  unfold tailWord_1320146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037420068835994957971073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32099786850229319887922861 12037420068835994957971073)
  ·
    refine ⟨9028065051626996218478305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12037420068835994957971073 9028065051626996218478305)
    ·
      refine ⟨6771048788720247163858729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9028065051626996218478305 6771048788720247163858729)
      ·
        refine ⟨5078286591540185372894047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6771048788720247163858729 5078286591540185372894047)
        ·
          refine ⟨7617429887310278059341071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5078286591540185372894047 7617429887310278059341071)
          ·
            refine ⟨11426144830965417089011607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7617429887310278059341071 11426144830965417089011607)
            ·
              refine ⟨17139217246448125633517411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11426144830965417089011607 17139217246448125633517411)
              ·
                refine ⟨25708825869672188450276117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17139217246448125633517411 25708825869672188450276117)
                ·
                  refine ⟨1205101212640883833606693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25708825869672188450276117 1205101212640883833606693)
                  ·
                    refine ⟨225956477370165718801255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205101212640883833606693 225956477370165718801255)
                    ·
                      rfl

theorem cell23_1320146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1320146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320146 prefixEnd_1320146 := by exact prefixLift 1320146
  have htrace : WordTrace (prefixWord ++ tailWord_1320146) baseStart_1320146 baseEnd_1320146 := by
    simpa [prefixWord, tailWord_1320146, baseEnd_1320146] using wordTrace_append hprefix tailTrace_1320146
  have hstable : (prefixWord ++ tailWord_1320146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320146).length < 2 ^ (prefixWord ++ tailWord_1320146).sum := by decide
  have hdescent : baseEnd_1320146 < baseStart_1320146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320169 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_1320169 : Nat := 118140960795 + 1320169 * 2 ^ 59
def prefixEnd_1320169 : Nat := 4983230072969 + 3 ^ 40 * 1320169 * 2
def baseEnd_1320169 : Nat := 677881242165550566416159

theorem tailTrace_1320169 : CollatzResearch.WordTrace tailWord_1320169 prefixEnd_1320169 677881242165550566416159 := by
  unfold tailWord_1320169
  simp only [CollatzResearch.WordTrace]
  refine ⟨48150519154260654759971561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32100346102840436506647707 48150519154260654759971561)
  ·
    refine ⟨36112889365695491069978671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48150519154260654759971561 36112889365695491069978671)
    ·
      refine ⟨54169334048543236604968007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36112889365695491069978671 54169334048543236604968007)
      ·
        refine ⟨81254001072814854907452011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54169334048543236604968007 81254001072814854907452011)
        ·
          refine ⟨121881001609222282361178017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81254001072814854907452011 121881001609222282361178017)
          ·
            refine ⟨91410751206916711770883513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121881001609222282361178017 91410751206916711770883513)
            ·
              refine ⟨68558063405187533828162635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91410751206916711770883513 68558063405187533828162635)
              ·
                refine ⟨102837095107781300742243953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68558063405187533828162635 102837095107781300742243953)
                ·
                  refine ⟨77127821330835975556682965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102837095107781300742243953 77127821330835975556682965)
                  ·
                    refine ⟨1807683312441468177109757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77127821330835975556682965 1807683312441468177109757)
                    ·
                      refine ⟨677881242165550566416159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807683312441468177109757 677881242165550566416159)
                      ·
                        rfl

theorem cell23_1320169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_1320169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320169 prefixEnd_1320169 := by exact prefixLift 1320169
  have htrace : WordTrace (prefixWord ++ tailWord_1320169) baseStart_1320169 baseEnd_1320169 := by
    simpa [prefixWord, tailWord_1320169, baseEnd_1320169] using wordTrace_append hprefix tailTrace_1320169
  have hstable : (prefixWord ++ tailWord_1320169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320169).length < 2 ^ (prefixWord ++ tailWord_1320169).sum := by decide
  have hdescent : baseEnd_1320169 < baseStart_1320169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320170 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_1320170 : Nat := 118140960795 + 1320170 * 2 ^ 59
def prefixEnd_1320170 : Nat := 4983230072969 + 3 ^ 40 * 1320170 * 2
def baseEnd_1320170 : Nat := 677881755646205062503655

theorem tailTrace_1320170 : CollatzResearch.WordTrace tailWord_1320170 prefixEnd_1320170 677881755646205062503655 := by
  unfold tailWord_1320170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037638906814257982689491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32100370418171354620505309 12037638906814257982689491)
  ·
    refine ⟨18056458360221386974034237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12037638906814257982689491 18056458360221386974034237)
    ·
      refine ⟨6771171885083020115262839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18056458360221386974034237 6771171885083020115262839)
      ·
        refine ⟨10156757827624530172894259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6771171885083020115262839 10156757827624530172894259)
        ·
          refine ⟨15235136741436795259341389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10156757827624530172894259 15235136741436795259341389)
          ·
            refine ⟨5713176278038798222253021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15235136741436795259341389 5713176278038798222253021)
            ·
              refine ⟨2142441104264549333344883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5713176278038798222253021 2142441104264549333344883)
              ·
                refine ⟨3213661656396824000017325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142441104264549333344883 3213661656396824000017325)
                ·
                  refine ⟨1205123121148809000006497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3213661656396824000017325 1205123121148809000006497)
                  ·
                    refine ⟨903842340861606750004873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205123121148809000006497 903842340861606750004873)
                    ·
                      refine ⟨677881755646205062503655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903842340861606750004873 677881755646205062503655)
                      ·
                        rfl

theorem cell23_1320170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_1320170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320170 prefixEnd_1320170 := by exact prefixLift 1320170
  have htrace : WordTrace (prefixWord ++ tailWord_1320170) baseStart_1320170 baseEnd_1320170 := by
    simpa [prefixWord, tailWord_1320170, baseEnd_1320170] using wordTrace_append hprefix tailTrace_1320170
  have hstable : (prefixWord ++ tailWord_1320170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320170).length < 2 ^ (prefixWord ++ tailWord_1320170).sum := by decide
  have hdescent : baseEnd_1320170 < baseStart_1320170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320186 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_1320186 : Nat := 118140960795 + 1320186 * 2 ^ 59
def prefixEnd_1320186 : Nat := 4983230072969 + 3 ^ 40 * 1320186 * 2
def baseEnd_1320186 : Nat := 677889971336676999903581

theorem tailTrace_1320186 : CollatzResearch.WordTrace tailWord_1320186 prefixEnd_1320186 677889971336676999903581 := by
  unfold tailWord_1320186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037784798799766665835103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32100759463466044442226941 12037784798799766665835103)
  ·
    refine ⟨18056677198199649998752655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12037784798799766665835103 18056677198199649998752655)
    ·
      refine ⟨27085015797299474998128983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18056677198199649998752655 27085015797299474998128983)
      ·
        refine ⟨40627523695949212497193475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27085015797299474998128983 40627523695949212497193475)
        ·
          refine ⟨60941285543923818745790213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40627523695949212497193475 60941285543923818745790213)
          ·
            refine ⟨11426491039485716014835665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60941285543923818745790213 11426491039485716014835665)
            ·
              refine ⟨8569868279614287011126749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11426491039485716014835665 8569868279614287011126749)
              ·
                refine ⟨3213700604855357629172531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8569868279614287011126749 3213700604855357629172531)
                ·
                  refine ⟨4820550907283036443758797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213700604855357629172531 4820550907283036443758797)
                  ·
                    refine ⟨1807706590231138666409549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4820550907283036443758797 1807706590231138666409549)
                    ·
                      refine ⟨677889971336676999903581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807706590231138666409549 677889971336676999903581)
                      ·
                        rfl

theorem cell23_1320186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_1320186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320186 prefixEnd_1320186 := by exact prefixLift 1320186
  have htrace : WordTrace (prefixWord ++ tailWord_1320186) baseStart_1320186 baseEnd_1320186 := by
    simpa [prefixWord, tailWord_1320186, baseEnd_1320186] using wordTrace_append hprefix tailTrace_1320186
  have hstable : (prefixWord ++ tailWord_1320186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320186).length < 2 ^ (prefixWord ++ tailWord_1320186).sum := by decide
  have hdescent : baseEnd_1320186 < baseStart_1320186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320190 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1320190 : Nat := 118140960795 + 1320190 * 2 ^ 59
def prefixEnd_1320190 : Nat := 4983230072969 + 3 ^ 40 * 1320190 * 2
def baseEnd_1320190 : Nat := 677892025259294984253563

theorem tailTrace_1320190 : CollatzResearch.WordTrace tailWord_1320190 prefixEnd_1320190 677892025259294984253563 := by
  unfold tailWord_1320190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6018910635898071918310753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32100856724789716897657349 6018910635898071918310753)
  ·
    refine ⟨4514182976923553938733065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6018910635898071918310753 4514182976923553938733065)
    ·
      refine ⟨3385637232692665454049799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4514182976923553938733065 3385637232692665454049799)
      ·
        refine ⟨5078455849038998181074699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3385637232692665454049799 5078455849038998181074699)
        ·
          refine ⟨7617683773558497271612049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5078455849038998181074699 7617683773558497271612049)
          ·
            refine ⟨5713262830168872953709037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7617683773558497271612049 5713262830168872953709037)
            ·
              refine ⟨2142473561313327357640889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5713262830168872953709037 2142473561313327357640889)
              ·
                refine ⟨1606855170984995518230667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142473561313327357640889 1606855170984995518230667)
                ·
                  refine ⟨2410282756477493277346001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606855170984995518230667 2410282756477493277346001)
                  ·
                    refine ⟨1807712067358119958009501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2410282756477493277346001 1807712067358119958009501)
                    ·
                      refine ⟨677892025259294984253563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807712067358119958009501 677892025259294984253563)
                      ·
                        rfl

theorem cell23_1320190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1320190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320190 prefixEnd_1320190 := by exact prefixLift 1320190
  have htrace : WordTrace (prefixWord ++ tailWord_1320190) baseStart_1320190 baseEnd_1320190 := by
    simpa [prefixWord, tailWord_1320190, baseEnd_1320190] using wordTrace_append hprefix tailTrace_1320190
  have hstable : (prefixWord ++ tailWord_1320190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320190).length < 2 ^ (prefixWord ++ tailWord_1320190).sum := by decide
  have hdescent : baseEnd_1320190 < baseStart_1320190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320219 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 2, 6]
def baseStart_1320219 : Nat := 118140960795 + 1320219 * 2 ^ 59
def prefixEnd_1320219 : Nat := 4983230072969 + 3 ^ 40 * 1320219 * 2
def baseEnd_1320219 : Nat := 225968972066091790263643

theorem tailTrace_1320219 : CollatzResearch.WordTrace tailWord_1320219 prefixEnd_1320219 225968972066091790263643 := by
  unfold tailWord_1320219
  simp only [CollatzResearch.WordTrace]
  refine ⟨48152342804079513299291711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32101561869386342199527807 48152342804079513299291711)
  ·
    refine ⟨72228514206119269948937567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48152342804079513299291711 72228514206119269948937567)
    ·
      refine ⟨108342771309178904923406351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72228514206119269948937567 108342771309178904923406351)
      ·
        refine ⟨162514156963768357385109527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108342771309178904923406351 162514156963768357385109527)
        ·
          refine ⟨243771235445652536077664291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162514156963768357385109527 243771235445652536077664291)
          ·
            refine ⟨365656853168478804116496437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243771235445652536077664291 365656853168478804116496437)
            ·
              refine ⟨34280329984544887885921541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365656853168478804116496437 34280329984544887885921541)
              ·
                refine ⟨6427561872102166478610289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34280329984544887885921541 6427561872102166478610289)
                ·
                  refine ⟨4820671404076624858957717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6427561872102166478610289 4820671404076624858957717)
                  ·
                    refine ⟨225968972066091790263643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4820671404076624858957717 225968972066091790263643)
                    ·
                      rfl

theorem cell23_1320219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_1320219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320219 prefixEnd_1320219 := by exact prefixLift 1320219
  have htrace : WordTrace (prefixWord ++ tailWord_1320219) baseStart_1320219 baseEnd_1320219 := by
    simpa [prefixWord, tailWord_1320219, baseEnd_1320219] using wordTrace_append hprefix tailTrace_1320219
  have hstable : (prefixWord ++ tailWord_1320219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320219).length < 2 ^ (prefixWord ++ tailWord_1320219).sum := by decide
  have hdescent : baseEnd_1320219 < baseStart_1320219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320221 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1320221 : Nat := 118140960795 + 1320221 * 2 ^ 59
def prefixEnd_1320221 : Nat := 4983230072969 + 3 ^ 40 * 1320221 * 2
def baseEnd_1320221 : Nat := 677907943159584362965921

theorem tailTrace_1320221 : CollatzResearch.WordTrace tailWord_1320221 prefixEnd_1320221 677907943159584362965921 := by
  unfold tailWord_1320221
  simp only [CollatzResearch.WordTrace]
  refine ⟨48152415750072267640864517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32101610500048178427243011 48152415750072267640864517)
  ·
    refine ⟨9028577953138550182662097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48152415750072267640864517 9028577953138550182662097)
    ·
      refine ⟨6771433464853912636996573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9028577953138550182662097 6771433464853912636996573)
      ·
        refine ⟨2539287549320217238873715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6771433464853912636996573 2539287549320217238873715)
        ·
          refine ⟨3808931323980325858310573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539287549320217238873715 3808931323980325858310573)
          ·
            refine ⟨1428349246492622196866465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3808931323980325858310573 1428349246492622196866465)
            ·
              refine ⟨1071261934869466647649849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428349246492622196866465 1071261934869466647649849)
              ·
                refine ⟨803446451152099985737387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071261934869466647649849 803446451152099985737387)
                ·
                  refine ⟨1205169676728149978606081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803446451152099985737387 1205169676728149978606081)
                  ·
                    refine ⟨903877257546112483954561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205169676728149978606081 903877257546112483954561)
                    ·
                      refine ⟨677907943159584362965921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903877257546112483954561 677907943159584362965921)
                      ·
                        rfl

theorem cell23_1320221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1320221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320221 prefixEnd_1320221 := by exact prefixLift 1320221
  have htrace : WordTrace (prefixWord ++ tailWord_1320221) baseStart_1320221 baseEnd_1320221 := by
    simpa [prefixWord, tailWord_1320221, baseEnd_1320221] using wordTrace_append hprefix tailTrace_1320221
  have hstable : (prefixWord ++ tailWord_1320221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320221).length < 2 ^ (prefixWord ++ tailWord_1320221).sum := by decide
  have hdescent : baseEnd_1320221 < baseStart_1320221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320237 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1320237 : Nat := 118140960795 + 1320237 * 2 ^ 59
def prefixEnd_1320237 : Nat := 4983230072969 + 3 ^ 40 * 1320237 * 2
def baseEnd_1320237 : Nat := 677916158850056300365847

theorem tailTrace_1320237 : CollatzResearch.WordTrace tailWord_1320237 prefixEnd_1320237 677916158850056300365847 := by
  unfold tailWord_1320237
  simp only [CollatzResearch.WordTrace]
  refine ⟨48152999318014302373446965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32101999545342868248964643 48152999318014302373446965)
  ·
    refine ⟨4514343686063840847510653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48152999318014302373446965 4514343686063840847510653)
    ·
      refine ⟨1692878882273940317816495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4514343686063840847510653 1692878882273940317816495)
      ·
        refine ⟨2539318323410910476724743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692878882273940317816495 2539318323410910476724743)
        ·
          refine ⟨3808977485116365715087115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539318323410910476724743 3808977485116365715087115)
          ·
            refine ⟨5713466227674548572630673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808977485116365715087115 5713466227674548572630673)
            ·
              refine ⟨4285099670755911429473005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713466227674548572630673 4285099670755911429473005)
              ·
                refine ⟨1606912376533466786052377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4285099670755911429473005 1606912376533466786052377)
                ·
                  refine ⟨1205184282400100089539283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606912376533466786052377 1205184282400100089539283)
                  ·
                    refine ⟨1807776423600150134308925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205184282400100089539283 1807776423600150134308925)
                    ·
                      refine ⟨677916158850056300365847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1807776423600150134308925 677916158850056300365847)
                      ·
                        rfl

theorem cell23_1320237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1320237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320237 prefixEnd_1320237 := by exact prefixLift 1320237
  have htrace : WordTrace (prefixWord ++ tailWord_1320237) baseStart_1320237 baseEnd_1320237 := by
    simpa [prefixWord, tailWord_1320237, baseEnd_1320237] using wordTrace_append hprefix tailTrace_1320237
  have hstable : (prefixWord ++ tailWord_1320237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320237).length < 2 ^ (prefixWord ++ tailWord_1320237).sum := by decide
  have hdescent : baseEnd_1320237 < baseStart_1320237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320243 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 1, 4, 2]
def baseStart_1320243 : Nat := 118140960795 + 1320243 * 2 ^ 59
def prefixEnd_1320243 : Nat := 4983230072969 + 3 ^ 40 * 1320243 * 2
def baseEnd_1320243 : Nat := 677919239733983276890819

theorem tailTrace_1320243 : CollatzResearch.WordTrace tailWord_1320243 prefixEnd_1320243 677919239733983276890819 := by
  unfold tailWord_1320243
  simp only [CollatzResearch.WordTrace]
  refine ⟨48153218155992565398165383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32102145437328376932110255 48153218155992565398165383)
  ·
    refine ⟨72229827233988848097248075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48153218155992565398165383 72229827233988848097248075)
    ·
      refine ⟨108344740850983272145872113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72229827233988848097248075 108344740850983272145872113)
      ·
        refine ⟨81258555638237454109404085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108344740850983272145872113 81258555638237454109404085)
        ·
          refine ⟨7617989591084761322756633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81258555638237454109404085 7617989591084761322756633)
          ·
            refine ⟨5713492193313570992067475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7617989591084761322756633 5713492193313570992067475)
            ·
              refine ⟨8570238289970356488101213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713492193313570992067475 8570238289970356488101213)
              ·
                refine ⟨3213839358738883683037955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8570238289970356488101213 3213839358738883683037955)
                ·
                  refine ⟨4820759038108325524556933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213839358738883683037955 4820759038108325524556933)
                  ·
                    refine ⟨903892319645311035854425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820759038108325524556933 903892319645311035854425)
                    ·
                      refine ⟨677919239733983276890819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903892319645311035854425 677919239733983276890819)
                      ·
                        rfl

theorem cell23_1320243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4, 2].length) (baseStart_1320243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320243 prefixEnd_1320243 := by exact prefixLift 1320243
  have htrace : WordTrace (prefixWord ++ tailWord_1320243) baseStart_1320243 baseEnd_1320243 := by
    simpa [prefixWord, tailWord_1320243, baseEnd_1320243] using wordTrace_append hprefix tailTrace_1320243
  have hstable : (prefixWord ++ tailWord_1320243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320243).length < 2 ^ (prefixWord ++ tailWord_1320243).sum := by decide
  have hdescent : baseEnd_1320243 < baseStart_1320243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320259 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1320259 : Nat := 118140960795 + 1320259 * 2 ^ 59
def prefixEnd_1320259 : Nat := 4983230072969 + 3 ^ 40 * 1320259 * 2
def baseEnd_1320259 : Nat := 677927455424455214290745

theorem tailTrace_1320259 : CollatzResearch.WordTrace tailWord_1320259 prefixEnd_1320259 677927455424455214290745 := by
  unfold tailWord_1320259
  simp only [CollatzResearch.WordTrace]
  refine ⟨48153801723934600130747831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32102534482623066753831887 48153801723934600130747831)
  ·
    refine ⟨72230702585901900196121747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48153801723934600130747831 72230702585901900196121747)
    ·
      refine ⟨108346053878852850294182621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72230702585901900196121747 108346053878852850294182621)
      ·
        refine ⟨40629770204569818860318483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108346053878852850294182621 40629770204569818860318483)
        ·
          refine ⟨60944655306854728290477725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40629770204569818860318483 60944655306854728290477725)
          ·
            refine ⟨22854245740070523108929147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60944655306854728290477725 22854245740070523108929147)
            ·
              refine ⟨34281368610105784663393721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22854245740070523108929147 34281368610105784663393721)
              ·
                refine ⟨25711026457579338497545291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34281368610105784663393721 25711026457579338497545291)
                ·
                  refine ⟨38566539686369007746317937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25711026457579338497545291 38566539686369007746317937)
                  ·
                    refine ⟨28924904764776755809738453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38566539686369007746317937 28924904764776755809738453)
                    ·
                      refine ⟨677927455424455214290745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28924904764776755809738453 677927455424455214290745)
                      ·
                        rfl

theorem cell23_1320259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1320259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320259 prefixEnd_1320259 := by exact prefixLift 1320259
  have htrace : WordTrace (prefixWord ++ tailWord_1320259) baseStart_1320259 baseEnd_1320259 := by
    simpa [prefixWord, tailWord_1320259, baseEnd_1320259] using wordTrace_append hprefix tailTrace_1320259
  have hstable : (prefixWord ++ tailWord_1320259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320259).length < 2 ^ (prefixWord ++ tailWord_1320259).sum := by decide
  have hdescent : baseEnd_1320259 < baseStart_1320259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320277 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_1320277 : Nat := 118140960795 + 1320277 * 2 ^ 59
def prefixEnd_1320277 : Nat := 4983230072969 + 3 ^ 40 * 1320277 * 2
def baseEnd_1320277 : Nat := 677936698076236143865663

theorem tailTrace_1320277 : CollatzResearch.WordTrace tailWord_1320277 prefixEnd_1320277 677936698076236143865663 := by
  unfold tailWord_1320277
  simp only [CollatzResearch.WordTrace]
  refine ⟨48154458237869389204903085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32102972158579592803268723 48154458237869389204903085)
  ·
    refine ⟨18057921839201020951838657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48154458237869389204903085 18057921839201020951838657)
    ·
      refine ⟨13543441379400765713878993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18057921839201020951838657 13543441379400765713878993)
      ·
        refine ⟨10157581034550574285409245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13543441379400765713878993 10157581034550574285409245)
        ·
          refine ⟨3809092887956465357028467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10157581034550574285409245 3809092887956465357028467)
          ·
            refine ⟨5713639331934698035542701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809092887956465357028467 5713639331934698035542701)
            ·
              refine ⟨2142614749475511763328513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5713639331934698035542701 2142614749475511763328513)
              ·
                refine ⟨1606961062106633822496385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142614749475511763328513 1606961062106633822496385)
                ·
                  refine ⟨1205220796579975366872289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606961062106633822496385 1205220796579975366872289)
                  ·
                    refine ⟨903915597434981525154217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205220796579975366872289 903915597434981525154217)
                    ·
                      refine ⟨677936698076236143865663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903915597434981525154217 677936698076236143865663)
                      ·
                        rfl

theorem cell23_1320277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_1320277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320277 prefixEnd_1320277 := by exact prefixLift 1320277
  have htrace : WordTrace (prefixWord ++ tailWord_1320277) baseStart_1320277 baseEnd_1320277 := by
    simpa [prefixWord, tailWord_1320277, baseEnd_1320277] using wordTrace_append hprefix tailTrace_1320277
  have hstable : (prefixWord ++ tailWord_1320277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320277).length < 2 ^ (prefixWord ++ tailWord_1320277).sum := by decide
  have hdescent : baseEnd_1320277 < baseStart_1320277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320316 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1320316 : Nat := 118140960795 + 1320316 * 2 ^ 59
def prefixEnd_1320316 : Nat := 4983230072969 + 3 ^ 40 * 1320316 * 2
def baseEnd_1320316 : Nat := 677956723821761491277983

theorem tailTrace_1320316 : CollatzResearch.WordTrace tailWord_1320316 prefixEnd_1320316 677956723821761491277983 := by
  unfold tailWord_1320316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077940342364049432786401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32103920456485399243715201 24077940342364049432786401)
  ·
    refine ⟨18058455256773037074589801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24077940342364049432786401 18058455256773037074589801)
    ·
      refine ⟨13543841442579777805942351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18058455256773037074589801 13543841442579777805942351)
      ·
        refine ⟨20315762163869666708913527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13543841442579777805942351 20315762163869666708913527)
        ·
          refine ⟨30473643245804500063370291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20315762163869666708913527 30473643245804500063370291)
          ·
            refine ⟨45710464868706750095055437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30473643245804500063370291 45710464868706750095055437)
            ·
              refine ⟨17141424325765031285645789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45710464868706750095055437 17141424325765031285645789)
              ·
                refine ⟨6428034122161886732117171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17141424325765031285645789 6428034122161886732117171)
                ·
                  refine ⟨9642051183242830098175757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6428034122161886732117171 9642051183242830098175757)
                  ·
                    refine ⟨3615769193716061286815909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9642051183242830098175757 3615769193716061286815909)
                    ·
                      refine ⟨677956723821761491277983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3615769193716061286815909 677956723821761491277983)
                      ·
                        rfl

theorem cell23_1320316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1320316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320316 prefixEnd_1320316 := by exact prefixLift 1320316
  have htrace : WordTrace (prefixWord ++ tailWord_1320316) baseStart_1320316 baseEnd_1320316 := by
    simpa [prefixWord, tailWord_1320316, baseEnd_1320316] using wordTrace_append hprefix tailTrace_1320316
  have hstable : (prefixWord ++ tailWord_1320316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320316).length < 2 ^ (prefixWord ++ tailWord_1320316).sum := by decide
  have hdescent : baseEnd_1320316 < baseStart_1320316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320393 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 3, 5, 2]
def baseStart_1320393 : Nat := 118140960795 + 1320393 * 2 ^ 59
def prefixEnd_1320393 : Nat := 4983230072969 + 3 ^ 40 * 1320393 * 2
def baseEnd_1320393 : Nat := 677996261832157690015129

theorem tailTrace_1320393 : CollatzResearch.WordTrace tailWord_1320393 prefixEnd_1320393 677996261832157690015129 := by
  unfold tailWord_1320393
  simp only [CollatzResearch.WordTrace]
  refine ⟨48158689105449141016125833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32105792736966094010750555 48158689105449141016125833)
  ·
    refine ⟨36119016829086855762094375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48158689105449141016125833 36119016829086855762094375)
    ·
      refine ⟨54178525243630283643141563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36119016829086855762094375 54178525243630283643141563)
      ·
        refine ⟨81267787865445425464712345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54178525243630283643141563 81267787865445425464712345)
        ·
          refine ⟨60950840899084069098534259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81267787865445425464712345 60950840899084069098534259)
          ·
            refine ⟨91426261348626103647801389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60950840899084069098534259 91426261348626103647801389)
            ·
              refine ⟨34284848005734788867925521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91426261348626103647801389 34284848005734788867925521)
              ·
                refine ⟨25713636004301091650944141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34284848005734788867925521 25713636004301091650944141)
                ·
                  refine ⟨9642613501612909369104053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25713636004301091650944141 9642613501612909369104053)
                  ·
                    refine ⟨903995015776210253353505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9642613501612909369104053 903995015776210253353505)
                    ·
                      refine ⟨677996261832157690015129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 903995015776210253353505 677996261832157690015129)
                      ·
                        rfl

theorem cell23_1320393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 5, 2].length) (baseStart_1320393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320393 prefixEnd_1320393 := by exact prefixLift 1320393
  have htrace : WordTrace (prefixWord ++ tailWord_1320393) baseStart_1320393 baseEnd_1320393 := by
    simpa [prefixWord, tailWord_1320393, baseEnd_1320393] using wordTrace_append hprefix tailTrace_1320393
  have hstable : (prefixWord ++ tailWord_1320393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320393).length < 2 ^ (prefixWord ++ tailWord_1320393).sum := by decide
  have hdescent : baseEnd_1320393 < baseStart_1320393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320394 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_1320394 : Nat := 118140960795 + 1320394 * 2 ^ 59
def prefixEnd_1320394 : Nat := 4983230072969 + 3 ^ 40 * 1320394 * 2
def baseEnd_1320394 : Nat := 225998925104270728700875

theorem tailTrace_1320394 : CollatzResearch.WordTrace tailWord_1320394 prefixEnd_1320394 225998925104270728700875 := by
  unfold tailWord_1320394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12039681394611379546728059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32105817052297012124608157 12039681394611379546728059)
  ·
    refine ⟨18059522091917069320092089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12039681394611379546728059 18059522091917069320092089)
    ·
      refine ⟨13544641568937801990069067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18059522091917069320092089 13544641568937801990069067)
      ·
        refine ⟨20316962353406702985103601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13544641568937801990069067 20316962353406702985103601)
        ·
          refine ⟨15237721765055027238827701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20316962353406702985103601 15237721765055027238827701)
          ·
            refine ⟨1428536415473908803640097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15237721765055027238827701 1428536415473908803640097)
            ·
              refine ⟨1071402311605431602730073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428536415473908803640097 1071402311605431602730073)
              ·
                refine ⟨803551733704073702047555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071402311605431602730073 803551733704073702047555)
                ·
                  refine ⟨1205327600556110553071333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803551733704073702047555 1205327600556110553071333)
                  ·
                    refine ⟨225998925104270728700875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205327600556110553071333 225998925104270728700875)
                    ·
                      rfl

theorem cell23_1320394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_1320394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320394 prefixEnd_1320394 := by exact prefixLift 1320394
  have htrace : WordTrace (prefixWord ++ tailWord_1320394) baseStart_1320394 baseEnd_1320394 := by
    simpa [prefixWord, tailWord_1320394, baseEnd_1320394] using wordTrace_append hprefix tailTrace_1320394
  have hstable : (prefixWord ++ tailWord_1320394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320394).length < 2 ^ (prefixWord ++ tailWord_1320394).sum := by decide
  have hdescent : baseEnd_1320394 < baseStart_1320394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320433 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1320433 : Nat := 118140960795 + 1320433 * 2 ^ 59
def prefixEnd_1320433 : Nat := 4983230072969 + 3 ^ 40 * 1320433 * 2
def baseEnd_1320433 : Nat := 226005600352779177838315

theorem tailTrace_1320433 : CollatzResearch.WordTrace tailWord_1320433 prefixEnd_1320433 226005600352779177838315 := by
  unfold tailWord_1320433
  simp only [CollatzResearch.WordTrace]
  refine ⟨48160148025304227847581953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32106765350202818565054635 48160148025304227847581953)
  ·
    refine ⟨36120111018978170885686465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48160148025304227847581953 36120111018978170885686465)
    ·
      refine ⟨27090083264233628164264849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36120111018978170885686465 27090083264233628164264849)
      ·
        refine ⟨20317562448175221123198637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27090083264233628164264849 20317562448175221123198637)
        ·
          refine ⟨7619085918065707921199489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20317562448175221123198637 7619085918065707921199489)
          ·
            refine ⟨5714314438549280940899617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7619085918065707921199489 5714314438549280940899617)
            ·
              refine ⟨4285735828911960705674713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5714314438549280940899617 4285735828911960705674713)
              ·
                refine ⟨3214301871683970529256035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285735828911960705674713 3214301871683970529256035)
                ·
                  refine ⟨4821452807525955793884053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214301871683970529256035 4821452807525955793884053)
                  ·
                    refine ⟨226005600352779177838315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4821452807525955793884053 226005600352779177838315)
                    ·
                      rfl

theorem cell23_1320433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1320433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320433 prefixEnd_1320433 := by exact prefixLift 1320433
  have htrace : WordTrace (prefixWord ++ tailWord_1320433) baseStart_1320433 baseEnd_1320433 := by
    simpa [prefixWord, tailWord_1320433, baseEnd_1320433] using wordTrace_append hprefix tailTrace_1320433
  have hstable : (prefixWord ++ tailWord_1320433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320433).length < 2 ^ (prefixWord ++ tailWord_1320433).sum := by decide
  have hdescent : baseEnd_1320433 < baseStart_1320433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320434 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1320434 : Nat := 118140960795 + 1320434 * 2 ^ 59
def prefixEnd_1320434 : Nat := 4983230072969 + 3 ^ 40 * 1320434 * 2
def baseEnd_1320434 : Nat := 678017314538992029602441

theorem tailTrace_1320434 : CollatzResearch.WordTrace tailWord_1320434 prefixEnd_1320434 678017314538992029602441 := by
  unfold tailWord_1320434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12040046124575151254592089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32106789665533736678912237 12040046124575151254592089)
  ·
    refine ⟨9030034593431363440944067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12040046124575151254592089 9030034593431363440944067)
    ·
      refine ⟨13545051890147045161416101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9030034593431363440944067 13545051890147045161416101)
      ·
        refine ⟨2539697229402570967765519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13545051890147045161416101 2539697229402570967765519)
        ·
          refine ⟨3809545844103856451648279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539697229402570967765519 3809545844103856451648279)
          ·
            refine ⟨5714318766155784677472419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809545844103856451648279 5714318766155784677472419)
            ·
              refine ⟨8571478149233677016208629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5714318766155784677472419 8571478149233677016208629)
              ·
                refine ⟨803576076490657220269559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8571478149233677016208629 803576076490657220269559)
                ·
                  refine ⟨1205364114735985830404339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803576076490657220269559 1205364114735985830404339)
                  ·
                    refine ⟨1808046172103978745606509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205364114735985830404339 1808046172103978745606509)
                    ·
                      refine ⟨678017314538992029602441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808046172103978745606509 678017314538992029602441)
                      ·
                        rfl

theorem cell23_1320434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1320434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320434 prefixEnd_1320434 := by exact prefixLift 1320434
  have htrace : WordTrace (prefixWord ++ tailWord_1320434) baseStart_1320434 baseEnd_1320434 := by
    simpa [prefixWord, tailWord_1320434, baseEnd_1320434] using wordTrace_append hprefix tailTrace_1320434
  have hstable : (prefixWord ++ tailWord_1320434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320434).length < 2 ^ (prefixWord ++ tailWord_1320434).sum := by decide
  have hdescent : baseEnd_1320434 < baseStart_1320434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320437 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1320437 : Nat := 118140960795 + 1320437 * 2 ^ 59
def prefixEnd_1320437 : Nat := 4983230072969 + 3 ^ 40 * 1320437 * 2
def baseEnd_1320437 : Nat := 226006284993651839288309

theorem tailTrace_1320437 : CollatzResearch.WordTrace tailWord_1320437 prefixEnd_1320437 226006284993651839288309 := by
  unfold tailWord_1320437
  simp only [CollatzResearch.WordTrace]
  refine ⟨48160293917289736530727565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32106862611526491020485043 48160293917289736530727565)
  ·
    refine ⟨18060110218983651199022837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48160293917289736530727565 18060110218983651199022837)
    ·
      refine ⟨1693135333029717299908391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18060110218983651199022837 1693135333029717299908391)
      ·
        refine ⟨2539702999544575949862587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693135333029717299908391 2539702999544575949862587)
        ·
          refine ⟨3809554499316863924793881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539702999544575949862587 3809554499316863924793881)
          ·
            refine ⟨2857165874487647943595411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3809554499316863924793881 2857165874487647943595411)
            ·
              refine ⟨4285748811731471915393117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857165874487647943595411 4285748811731471915393117)
              ·
                refine ⟨1607155804399301968272419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4285748811731471915393117 1607155804399301968272419)
                ·
                  refine ⟨2410733706598952952408629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607155804399301968272419 2410733706598952952408629)
                  ·
                    refine ⟨226006284993651839288309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2410733706598952952408629 226006284993651839288309)
                    ·
                      rfl

theorem cell23_1320437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1320437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320437 prefixEnd_1320437 := by exact prefixLift 1320437
  have htrace : WordTrace (prefixWord ++ tailWord_1320437) baseStart_1320437 baseEnd_1320437 := by
    simpa [prefixWord, tailWord_1320437, baseEnd_1320437] using wordTrace_append hprefix tailTrace_1320437
  have hstable : (prefixWord ++ tailWord_1320437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320437).length < 2 ^ (prefixWord ++ tailWord_1320437).sum := by decide
  have hdescent : baseEnd_1320437 < baseStart_1320437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320440 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_1320440 : Nat := 118140960795 + 1320440 * 2 ^ 59
def prefixEnd_1320440 : Nat := 4983230072969 + 3 ^ 40 * 1320440 * 2
def baseEnd_1320440 : Nat := 678020395422919006127413

theorem tailTrace_1320440 : CollatzResearch.WordTrace tailWord_1320440 prefixEnd_1320440 678020395422919006127413 := by
  unfold tailWord_1320440
  simp only [CollatzResearch.WordTrace]
  refine ⟨24080201668139434021543387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32106935557519245362057849 24080201668139434021543387)
  ·
    refine ⟨36120302502209151032315081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24080201668139434021543387 36120302502209151032315081)
    ·
      refine ⟨27090226876656863274236311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36120302502209151032315081 27090226876656863274236311)
      ·
        refine ⟨40635340314985294911354467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27090226876656863274236311 40635340314985294911354467)
        ·
          refine ⟨60953010472477942367031701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40635340314985294911354467 60953010472477942367031701)
          ·
            refine ⟨2857172365897403548454611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60953010472477942367031701 2857172365897403548454611)
            ·
              refine ⟨4285758548846105322681917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857172365897403548454611 4285758548846105322681917)
              ·
                refine ⟨1607159455817289496005719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4285758548846105322681917 1607159455817289496005719)
                ·
                  refine ⟨2410739183725934244008579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607159455817289496005719 2410739183725934244008579)
                  ·
                    refine ⟨3616108775588901366012869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2410739183725934244008579 3616108775588901366012869)
                    ·
                      refine ⟨678020395422919006127413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3616108775588901366012869 678020395422919006127413)
                      ·
                        rfl

theorem cell23_1320440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_1320440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320440 prefixEnd_1320440 := by exact prefixLift 1320440
  have htrace : WordTrace (prefixWord ++ tailWord_1320440) baseStart_1320440 baseEnd_1320440 := by
    simpa [prefixWord, tailWord_1320440, baseEnd_1320440] using wordTrace_append hprefix tailTrace_1320440
  have hstable : (prefixWord ++ tailWord_1320440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320440).length < 2 ^ (prefixWord ++ tailWord_1320440).sum := by decide
  have hdescent : baseEnd_1320440 < baseStart_1320440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320457 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 3, 2, 2]
def baseStart_1320457 : Nat := 118140960795 + 1320457 * 2 ^ 59
def prefixEnd_1320457 : Nat := 4983230072969 + 3 ^ 40 * 1320457 * 2
def baseEnd_1320457 : Nat := 678029124594045439614835

theorem tailTrace_1320457 : CollatzResearch.WordTrace tailWord_1320457 prefixEnd_1320457 678029124594045439614835 := by
  unfold tailWord_1320457
  simp only [CollatzResearch.WordTrace]
  refine ⟨48161023377217279946455625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32107348918144853297637083 48161023377217279946455625)
  ·
    refine ⟨36120767532912959959841719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48161023377217279946455625 36120767532912959959841719)
    ·
      refine ⟨54181151299369439939762579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36120767532912959959841719 54181151299369439939762579)
      ·
        refine ⟨81271726949054159909643869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54181151299369439939762579 81271726949054159909643869)
        ·
          refine ⟨30476897605895309966116451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81271726949054159909643869 30476897605895309966116451)
          ·
            refine ⟨45715346408842964949174677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30476897605895309966116451 45715346408842964949174677)
            ·
              refine ⟨2142906862914513981992563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45715346408842964949174677 2142906862914513981992563)
              ·
                refine ⟨3214360294371770972988845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142906862914513981992563 3214360294371770972988845)
                ·
                  refine ⟨1205385110389414114870817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3214360294371770972988845 1205385110389414114870817)
                  ·
                    refine ⟨904038832792060586153113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205385110389414114870817 904038832792060586153113)
                    ·
                      refine ⟨678029124594045439614835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904038832792060586153113 678029124594045439614835)
                      ·
                        rfl

theorem cell23_1320457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 2, 2].length) (baseStart_1320457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320457 prefixEnd_1320457 := by exact prefixLift 1320457
  have htrace : WordTrace (prefixWord ++ tailWord_1320457) baseStart_1320457 baseEnd_1320457 := by
    simpa [prefixWord, tailWord_1320457, baseEnd_1320457] using wordTrace_append hprefix tailTrace_1320457
  have hstable : (prefixWord ++ tailWord_1320457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320457).length < 2 ^ (prefixWord ++ tailWord_1320457).sum := by decide
  have hdescent : baseEnd_1320457 < baseStart_1320457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320460 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1320460 : Nat := 118140960795 + 1320460 * 2 ^ 59
def prefixEnd_1320460 : Nat := 4983230072969 + 3 ^ 40 * 1320460 * 2
def baseEnd_1320460 : Nat := 678030665036008927877321

theorem tailTrace_1320460 : CollatzResearch.WordTrace tailWord_1320460 prefixEnd_1320460 678030665036008927877321 := by
  unfold tailWord_1320460
  simp only [CollatzResearch.WordTrace]
  refine ⟨24080566398103205729407417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32107421864137607639209889 24080566398103205729407417)
  ·
    refine ⟨18060424798577404297055563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24080566398103205729407417 18060424798577404297055563)
    ·
      refine ⟨27090637197866106445583345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18060424798577404297055563 27090637197866106445583345)
      ·
        refine ⟨20317977898399579834187509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27090637197866106445583345 20317977898399579834187509)
        ·
          refine ⟨1904810427974960609455079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20317977898399579834187509 1904810427974960609455079)
          ·
            refine ⟨2857215641962440914182619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904810427974960609455079 2857215641962440914182619)
            ·
              refine ⟨4285823462943661371273929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857215641962440914182619 4285823462943661371273929)
              ·
                refine ⟨3214367597207746028455447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285823462943661371273929 3214367597207746028455447)
                ·
                  refine ⟨4821551395811619042683171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214367597207746028455447 4821551395811619042683171)
                  ·
                    refine ⟨7232327093717428564024757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4821551395811619042683171 7232327093717428564024757)
                    ·
                      refine ⟨678030665036008927877321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7232327093717428564024757 678030665036008927877321)
                      ·
                        rfl

theorem cell23_1320460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1320460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320460 prefixEnd_1320460 := by exact prefixLift 1320460
  have htrace : WordTrace (prefixWord ++ tailWord_1320460) baseStart_1320460 baseEnd_1320460 := by
    simpa [prefixWord, tailWord_1320460, baseEnd_1320460] using wordTrace_append hprefix tailTrace_1320460
  have hstable : (prefixWord ++ tailWord_1320460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320460).length < 2 ^ (prefixWord ++ tailWord_1320460).sum := by decide
  have hdescent : baseEnd_1320460 < baseStart_1320460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320467 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 2, 4]
def baseStart_1320467 : Nat := 118140960795 + 1320467 * 2 ^ 59
def prefixEnd_1320467 : Nat := 4983230072969 + 3 ^ 40 * 1320467 * 2
def baseEnd_1320467 : Nat := 226011419800196800163263

theorem tailTrace_1320467 : CollatzResearch.WordTrace tailWord_1320467 prefixEnd_1320467 226011419800196800163263 := by
  unfold tailWord_1320467
  simp only [CollatzResearch.WordTrace]
  refine ⟨48161388107181051654319655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32107592071454034436213103 48161388107181051654319655)
  ·
    refine ⟨72242082160771577481479483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48161388107181051654319655 72242082160771577481479483)
    ·
      refine ⟨108363123241157366222219225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72242082160771577481479483 108363123241157366222219225)
      ·
        refine ⟨81272342430868024666664419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108363123241157366222219225 81272342430868024666664419)
        ·
          refine ⟨121908513646302036999996629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81272342430868024666664419 121908513646302036999996629)
          ·
            refine ⟨2857230788585203992187421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 121908513646302036999996629 2857230788585203992187421)
            ·
              refine ⟨1071461545719451497070283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2857230788585203992187421 1071461545719451497070283)
              ·
                refine ⟨1607192318579177245605425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071461545719451497070283 1607192318579177245605425)
                ·
                  refine ⟨1205394238934382934204069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1607192318579177245605425 1205394238934382934204069)
                  ·
                    refine ⟨226011419800196800163263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205394238934382934204069 226011419800196800163263)
                    ·
                      rfl

theorem cell23_1320467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 4].length) (baseStart_1320467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320467 prefixEnd_1320467 := by exact prefixLift 1320467
  have htrace : WordTrace (prefixWord ++ tailWord_1320467) baseStart_1320467 baseEnd_1320467 := by
    simpa [prefixWord, tailWord_1320467, baseEnd_1320467] using wordTrace_append hprefix tailTrace_1320467
  have hstable : (prefixWord ++ tailWord_1320467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320467).length < 2 ^ (prefixWord ++ tailWord_1320467).sum := by decide
  have hdescent : baseEnd_1320467 < baseStart_1320467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320477 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1320477 : Nat := 118140960795 + 1320477 * 2 ^ 59
def prefixEnd_1320477 : Nat := 4983230072969 + 3 ^ 40 * 1320477 * 2
def baseEnd_1320477 : Nat := 678039394207135361364743

theorem tailTrace_1320477 : CollatzResearch.WordTrace tailWord_1320477 prefixEnd_1320477 678039394207135361364743 := by
  unfold tailWord_1320477
  simp only [CollatzResearch.WordTrace]
  refine ⟨48161752837144823362183685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32107835224763215574789123 48161752837144823362183685)
  ·
    refine ⟨9030328656964654380409441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48161752837144823362183685 9030328656964654380409441)
    ·
      refine ⟨6772746492723490785307081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9030328656964654380409441 6772746492723490785307081)
      ·
        refine ⟨5079559869542618088980311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6772746492723490785307081 5079559869542618088980311)
        ·
          refine ⟨7619339804313927133470467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5079559869542618088980311 7619339804313927133470467)
          ·
            refine ⟨11429009706470890700205701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7619339804313927133470467 11429009706470890700205701)
            ·
              refine ⟨2142939319963292006288569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11429009706470890700205701 2142939319963292006288569)
              ·
                refine ⟨1607204489972469004716427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142939319963292006288569 1607204489972469004716427)
                ·
                  refine ⟨2410806734958703507074641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607204489972469004716427 2410806734958703507074641)
                  ·
                    refine ⟨1808105051219027630305981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2410806734958703507074641 1808105051219027630305981)
                    ·
                      refine ⟨678039394207135361364743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808105051219027630305981 678039394207135361364743)
                      ·
                        rfl

theorem cell23_1320477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1320477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320477 prefixEnd_1320477 := by exact prefixLift 1320477
  have htrace : WordTrace (prefixWord ++ tailWord_1320477) baseStart_1320477 baseEnd_1320477 := by
    simpa [prefixWord, tailWord_1320477, baseEnd_1320477] using wordTrace_append hprefix tailTrace_1320477
  have hstable : (prefixWord ++ tailWord_1320477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320477).length < 2 ^ (prefixWord ++ tailWord_1320477).sum := by decide
  have hdescent : baseEnd_1320477 < baseStart_1320477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320480 : List Nat := [2, 1, 1, 6, 1, 1, 4, 7]
def baseStart_1320480 : Nat := 118140960795 + 1320480 * 2 ^ 59
def prefixEnd_1320480 : Nat := 4983230072969 + 3 ^ 40 * 1320480 * 2
def baseEnd_1320480 : Nat := 25112627209225883319527

theorem tailTrace_1320480 : CollatzResearch.WordTrace tailWord_1320480 prefixEnd_1320480 25112627209225883319527 := by
  unfold tailWord_1320480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24080931128066977437271447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32107908170755969916361929 24080931128066977437271447)
  ·
    refine ⟨36121396692100466155907171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24080931128066977437271447 36121396692100466155907171)
    ·
      refine ⟨54182095038150699233860757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36121396692100466155907171 54182095038150699233860757)
      ·
        refine ⟨2539785704913314026587223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54182095038150699233860757 2539785704913314026587223)
        ·
          refine ⟨3809678557369971039880835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539785704913314026587223 3809678557369971039880835)
          ·
            refine ⟨5714517836054956559821253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809678557369971039880835 5714517836054956559821253)
            ·
              refine ⟨1071472094260304354966485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5714517836054956559821253 1071472094260304354966485)
              ·
                refine ⟨25112627209225883319527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1071472094260304354966485 25112627209225883319527)
                ·
                  rfl

theorem cell23_1320480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 7].length) (baseStart_1320480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320480 prefixEnd_1320480 := by exact prefixLift 1320480
  have htrace : WordTrace (prefixWord ++ tailWord_1320480) baseStart_1320480 baseEnd_1320480 := by
    simpa [prefixWord, tailWord_1320480, baseEnd_1320480] using wordTrace_append hprefix tailTrace_1320480
  have hstable : (prefixWord ++ tailWord_1320480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320480).length < 2 ^ (prefixWord ++ tailWord_1320480).sum := by decide
  have hdescent : baseEnd_1320480 < baseStart_1320480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320490 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1320490 : Nat := 118140960795 + 1320490 * 2 ^ 59
def prefixEnd_1320490 : Nat := 4983230072969 + 3 ^ 40 * 1320490 * 2
def baseEnd_1320490 : Nat := 678046069455643810502183

theorem tailTrace_1320490 : CollatzResearch.WordTrace tailWord_1320490 prefixEnd_1320490 678046069455643810502183 := by
  unfold tailWord_1320490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12040556746524431645601731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32108151324065151054937949 12040556746524431645601731)
  ·
    refine ⟨18060835119786647468402597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12040556746524431645601731 18060835119786647468402597)
    ·
      refine ⟨3386406584959996400325487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18060835119786647468402597 3386406584959996400325487)
      ·
        refine ⟨5079609877439994600488231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386406584959996400325487 5079609877439994600488231)
        ·
          refine ⟨7619414816159991900732347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5079609877439994600488231 7619414816159991900732347)
          ·
            refine ⟨11429122224239987851098521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7619414816159991900732347 11429122224239987851098521)
            ·
              refine ⟨8571841668179990888323891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11429122224239987851098521 8571841668179990888323891)
              ·
                refine ⟨12857762502269986332485837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8571841668179990888323891 12857762502269986332485837)
                ·
                  refine ⟨4821660938351244874682189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12857762502269986332485837 4821660938351244874682189)
                  ·
                    refine ⟨1808122851881716828005821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4821660938351244874682189 1808122851881716828005821)
                    ·
                      refine ⟨678046069455643810502183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808122851881716828005821 678046069455643810502183)
                      ·
                        rfl

theorem cell23_1320490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1320490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320490 prefixEnd_1320490 := by exact prefixLift 1320490
  have htrace : WordTrace (prefixWord ++ tailWord_1320490) baseStart_1320490 baseEnd_1320490 := by
    simpa [prefixWord, tailWord_1320490, baseEnd_1320490] using wordTrace_append hprefix tailTrace_1320490
  have hstable : (prefixWord ++ tailWord_1320490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320490).length < 2 ^ (prefixWord ++ tailWord_1320490).sum := by decide
  have hdescent : baseEnd_1320490 < baseStart_1320490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320508 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_1320508 : Nat := 118140960795 + 1320508 * 2 ^ 59
def prefixEnd_1320508 : Nat := 4983230072969 + 3 ^ 40 * 1320508 * 2
def baseEnd_1320508 : Nat := 678055312107424740077101

theorem tailTrace_1320508 : CollatzResearch.WordTrace tailWord_1320508 prefixEnd_1320508 678055312107424740077101 := by
  unfold tailWord_1320508
  simp only [CollatzResearch.WordTrace]
  refine ⟨24081441750016257828281089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32108589000021677104374785 24081441750016257828281089)
  ·
    refine ⟨18061081312512193371210817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24081441750016257828281089 18061081312512193371210817)
    ·
      refine ⟨13545810984384145028408113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18061081312512193371210817 13545810984384145028408113)
      ·
        refine ⟨10159358238288108771306085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13545810984384145028408113 10159358238288108771306085)
        ·
          refine ⟨1904879669679020394619891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10159358238288108771306085 1904879669679020394619891)
          ·
            refine ⟨2857319504518530591929837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904879669679020394619891 2857319504518530591929837)
            ·
              refine ⟨1071494814194448971973689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2857319504518530591929837 1071494814194448971973689)
              ·
                refine ⟨803621110645836728980267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071494814194448971973689 803621110645836728980267)
                ·
                  refine ⟨1205431665968755093470401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803621110645836728980267 1205431665968755093470401)
                  ·
                    refine ⟨904073749476566320102801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205431665968755093470401 904073749476566320102801)
                    ·
                      refine ⟨678055312107424740077101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904073749476566320102801 678055312107424740077101)
                      ·
                        rfl

theorem cell23_1320508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_1320508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320508 prefixEnd_1320508 := by exact prefixLift 1320508
  have htrace : WordTrace (prefixWord ++ tailWord_1320508) baseStart_1320508 baseEnd_1320508 := by
    simpa [prefixWord, tailWord_1320508, baseEnd_1320508] using wordTrace_append hprefix tailTrace_1320508
  have hstable : (prefixWord ++ tailWord_1320508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320508).length < 2 ^ (prefixWord ++ tailWord_1320508).sum := by decide
  have hdescent : baseEnd_1320508 < baseStart_1320508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320518 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1320518 : Nat := 118140960795 + 1320518 * 2 ^ 59
def prefixEnd_1320518 : Nat := 4983230072969 + 3 ^ 40 * 1320518 * 2
def baseEnd_1320518 : Nat := 226020148971323233650685

theorem tailTrace_1320518 : CollatzResearch.WordTrace tailWord_1320518 prefixEnd_1320518 226020148971323233650685 := by
  unfold tailWord_1320518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505101507187383980138319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32108832153330858242950805 1505101507187383980138319)
  ·
    refine ⟨2257652260781075970207479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1505101507187383980138319 2257652260781075970207479)
    ·
      refine ⟨3386478391171613955311219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2257652260781075970207479 3386478391171613955311219)
      ·
        refine ⟨5079717586757420932966829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386478391171613955311219 5079717586757420932966829)
        ·
          refine ⟨1904894095034032849862561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5079717586757420932966829 1904894095034032849862561)
          ·
            refine ⟨1428670571275524637396921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904894095034032849862561 1428670571275524637396921)
            ·
              refine ⟨1071502928456643478047691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428670571275524637396921 1071502928456643478047691)
              ·
                refine ⟨1607254392684965217071537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071502928456643478047691 1607254392684965217071537)
                ·
                  refine ⟨1205440794513723912803653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1607254392684965217071537 1205440794513723912803653)
                  ·
                    refine ⟨226020148971323233650685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205440794513723912803653 226020148971323233650685)
                    ·
                      rfl

theorem cell23_1320518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1320518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320518 prefixEnd_1320518 := by exact prefixLift 1320518
  have htrace : WordTrace (prefixWord ++ tailWord_1320518) baseStart_1320518 baseEnd_1320518 := by
    simpa [prefixWord, tailWord_1320518, baseEnd_1320518] using wordTrace_append hprefix tailTrace_1320518
  have hstable : (prefixWord ++ tailWord_1320518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320518).length < 2 ^ (prefixWord ++ tailWord_1320518).sum := by decide
  have hdescent : baseEnd_1320518 < baseStart_1320518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320524 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1320524 : Nat := 118140960795 + 1320524 * 2 ^ 59
def prefixEnd_1320524 : Nat := 4983230072969 + 3 ^ 40 * 1320524 * 2
def baseEnd_1320524 : Nat := 678063527797896677477027

theorem tailTrace_1320524 : CollatzResearch.WordTrace tailWord_1320524 prefixEnd_1320524 678063527797896677477027 := by
  unfold tailWord_1320524
  simp only [CollatzResearch.WordTrace]
  refine ⟨24081733533987275194572313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32108978045316366926096417 24081733533987275194572313)
  ·
    refine ⟨18061300150490456395929235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24081733533987275194572313 18061300150490456395929235)
    ·
      refine ⟨27091950225735684593893853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18061300150490456395929235 27091950225735684593893853)
      ·
        refine ⟨10159481334650881722710195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27091950225735684593893853 10159481334650881722710195)
        ·
          refine ⟨15239222001976322584065293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159481334650881722710195 15239222001976322584065293)
          ·
            refine ⟨5714708250741120969024485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15239222001976322584065293 5714708250741120969024485)
            ·
              refine ⟨1071507797013960181692091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5714708250741120969024485 1071507797013960181692091)
              ·
                refine ⟨1607261695520940272538137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071507797013960181692091 1607261695520940272538137)
                ·
                  refine ⟨1205446271640705204403603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1607261695520940272538137 1205446271640705204403603)
                  ·
                    refine ⟨1808169407461057806605405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205446271640705204403603 1808169407461057806605405)
                    ·
                      refine ⟨678063527797896677477027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808169407461057806605405 678063527797896677477027)
                      ·
                        rfl

theorem cell23_1320524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1320524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320524 prefixEnd_1320524 := by exact prefixLift 1320524
  have htrace : WordTrace (prefixWord ++ tailWord_1320524) baseStart_1320524 baseEnd_1320524 := by
    simpa [prefixWord, tailWord_1320524, baseEnd_1320524] using wordTrace_append hprefix tailTrace_1320524
  have hstable : (prefixWord ++ tailWord_1320524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320524).length < 2 ^ (prefixWord ++ tailWord_1320524).sum := by decide
  have hdescent : baseEnd_1320524 < baseStart_1320524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320543 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1320543 : Nat := 118140960795 + 1320543 * 2 ^ 59
def prefixEnd_1320543 : Nat := 4983230072969 + 3 ^ 40 * 1320543 * 2
def baseEnd_1320543 : Nat := 678073283930332103139439

theorem tailTrace_1320543 : CollatzResearch.WordTrace tailWord_1320543 prefixEnd_1320543 678073283930332103139439 := by
  unfold tailWord_1320543
  simp only [CollatzResearch.WordTrace]
  refine ⟨48164160054905716634086283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32109440036603811089390855 48164160054905716634086283)
  ·
    refine ⟨72246240082358574951129425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48164160054905716634086283 72246240082358574951129425)
    ·
      refine ⟨54184680061768931213347069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72246240082358574951129425 54184680061768931213347069)
      ·
        refine ⟨20319255023163349205005151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54184680061768931213347069 20319255023163349205005151)
        ·
          refine ⟨30478882534745023807507727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20319255023163349205005151 30478882534745023807507727)
          ·
            refine ⟨45718323802117535711261591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30478882534745023807507727 45718323802117535711261591)
            ·
              refine ⟨68577485703176303566892387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45718323802117535711261591 68577485703176303566892387)
              ·
                refine ⟨102866228554764455350338581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68577485703176303566892387 102866228554764455350338581)
                ·
                  refine ⟨4821854463504583844547121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102866228554764455350338581 4821854463504583844547121)
                  ·
                    refine ⟨3616390847628437883410341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4821854463504583844547121 3616390847628437883410341)
                    ·
                      refine ⟨678073283930332103139439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3616390847628437883410341 678073283930332103139439)
                      ·
                        rfl

theorem cell23_1320543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1320543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320543 prefixEnd_1320543 := by exact prefixLift 1320543
  have htrace : WordTrace (prefixWord ++ tailWord_1320543) baseStart_1320543 baseEnd_1320543 := by
    simpa [prefixWord, tailWord_1320543, baseEnd_1320543] using wordTrace_append hprefix tailTrace_1320543
  have hstable : (prefixWord ++ tailWord_1320543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320543).length < 2 ^ (prefixWord ++ tailWord_1320543).sum := by decide
  have hdescent : baseEnd_1320543 < baseStart_1320543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320547 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 1, 4, 2]
def baseStart_1320547 : Nat := 118140960795 + 1320547 * 2 ^ 59
def prefixEnd_1320547 : Nat := 4983230072969 + 3 ^ 40 * 1320547 * 2
def baseEnd_1320547 : Nat := 678075337852950087489421

theorem tailTrace_1320547 : CollatzResearch.WordTrace tailWord_1320547 prefixEnd_1320547 678075337852950087489421 := by
  unfold tailWord_1320547
  simp only [CollatzResearch.WordTrace]
  refine ⟨48164305946891225317231895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32109537297927483544821263 48164305946891225317231895)
  ·
    refine ⟨72246458920336837975847843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48164305946891225317231895 72246458920336837975847843)
    ·
      refine ⟨108369688380505256963771765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72246458920336837975847843 108369688380505256963771765)
      ·
        refine ⟨10159658285672367840353603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108369688380505256963771765 10159658285672367840353603)
        ·
          refine ⟨15239487428508551760530405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159658285672367840353603 15239487428508551760530405)
          ·
            refine ⟨2857403892845353455099451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15239487428508551760530405 2857403892845353455099451)
            ·
              refine ⟨4286105839268030182649177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857403892845353455099451 4286105839268030182649177)
              ·
                refine ⟨3214579379451022636986883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4286105839268030182649177 3214579379451022636986883)
                ·
                  refine ⟨4821869069176533955480325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214579379451022636986883 4821869069176533955480325)
                  ·
                    refine ⟨904100450470600116652561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821869069176533955480325 904100450470600116652561)
                    ·
                      refine ⟨678075337852950087489421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904100450470600116652561 678075337852950087489421)
                      ·
                        rfl

theorem cell23_1320547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_1320547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320547 prefixEnd_1320547 := by exact prefixLift 1320547
  have htrace : WordTrace (prefixWord ++ tailWord_1320547) baseStart_1320547 baseEnd_1320547 := by
    simpa [prefixWord, tailWord_1320547, baseEnd_1320547] using wordTrace_append hprefix tailTrace_1320547
  have hstable : (prefixWord ++ tailWord_1320547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320547).length < 2 ^ (prefixWord ++ tailWord_1320547).sum := by decide
  have hdescent : baseEnd_1320547 < baseStart_1320547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320593 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_1320593 : Nat := 118140960795 + 1320593 * 2 ^ 59
def prefixEnd_1320593 : Nat := 4983230072969 + 3 ^ 40 * 1320593 * 2
def baseEnd_1320593 : Nat := 678098957963056907514209

theorem tailTrace_1320593 : CollatzResearch.WordTrace tailWord_1320593 prefixEnd_1320593 678098957963056907514209 := by
  unfold tailWord_1320593
  simp only [CollatzResearch.WordTrace]
  refine ⟨48165983704724575173406433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32110655803149716782270955 48165983704724575173406433)
  ·
    refine ⟨36124487778543431380054825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48165983704724575173406433 36124487778543431380054825)
    ·
      refine ⟨27093365833907573535041119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36124487778543431380054825 27093365833907573535041119)
      ·
        refine ⟨40640048750861360302561679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27093365833907573535041119 40640048750861360302561679)
        ·
          refine ⟨60960073126292040453842519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40640048750861360302561679 60960073126292040453842519)
          ·
            refine ⟨91440109689438060680763779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60960073126292040453842519 91440109689438060680763779)
            ·
              refine ⟨137160164534157091021145669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91440109689438060680763779 137160164534157091021145669)
              ·
                refine ⟨25717530850154454566464813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137160164534157091021145669 25717530850154454566464813)
                ·
                  refine ⟨9644074068807920462424305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25717530850154454566464813 9644074068807920462424305)
                  ·
                    refine ⟨7233055551605940346818229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9644074068807920462424305 7233055551605940346818229)
                    ·
                      refine ⟨678098957963056907514209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7233055551605940346818229 678098957963056907514209)
                      ·
                        rfl

theorem cell23_1320593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_1320593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320593 prefixEnd_1320593 := by exact prefixLift 1320593
  have htrace : WordTrace (prefixWord ++ tailWord_1320593) baseStart_1320593 baseEnd_1320593 := by
    simpa [prefixWord, tailWord_1320593, baseEnd_1320593] using wordTrace_append hprefix tailTrace_1320593
  have hstable : (prefixWord ++ tailWord_1320593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320593).length < 2 ^ (prefixWord ++ tailWord_1320593).sum := by decide
  have hdescent : baseEnd_1320593 < baseStart_1320593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320600 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_1320600 : Nat := 118140960795 + 1320600 * 2 ^ 59
def prefixEnd_1320600 : Nat := 4983230072969 + 3 ^ 40 * 1320600 * 2
def baseEnd_1320600 : Nat := 226034184109212793375559

theorem tailTrace_1320600 : CollatzResearch.WordTrace tailWord_1320600 prefixEnd_1320600 226034184109212793375559 := by
  unfold tailWord_1320600
  simp only [CollatzResearch.WordTrace]
  refine ⟨24083119507849607684455627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32110826010466143579274169 24083119507849607684455627)
  ·
    refine ⟨36124679261774411526683441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24083119507849607684455627 36124679261774411526683441)
    ·
      refine ⟨27093509446330808645012581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36124679261774411526683441 27093509446330808645012581)
      ·
        refine ⟨5080033021187026620939859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27093509446330808645012581 5080033021187026620939859)
        ·
          refine ⟨7620049531780539931409789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5080033021187026620939859 7620049531780539931409789)
          ·
            refine ⟨2857518574417702474278671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7620049531780539931409789 2857518574417702474278671)
            ·
              refine ⟨4286277861626553711418007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857518574417702474278671 4286277861626553711418007)
              ·
                refine ⟨6429416792439830567127011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286277861626553711418007 6429416792439830567127011)
                ·
                  refine ⟨9644125188659745850690517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429416792439830567127011 9644125188659745850690517)
                  ·
                    refine ⟨226034184109212793375559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9644125188659745850690517 226034184109212793375559)
                    ·
                      rfl

theorem cell23_1320600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_1320600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320600 prefixEnd_1320600 := by exact prefixLift 1320600
  have htrace : WordTrace (prefixWord ++ tailWord_1320600) baseStart_1320600 baseEnd_1320600 := by
    simpa [prefixWord, tailWord_1320600, baseEnd_1320600] using wordTrace_append hprefix tailTrace_1320600
  have hstable : (prefixWord ++ tailWord_1320600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320600).length < 2 ^ (prefixWord ++ tailWord_1320600).sum := by decide
  have hdescent : baseEnd_1320600 < baseStart_1320600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320604 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 5]
def baseStart_1320604 : Nat := 118140960795 + 1320604 * 2 ^ 59
def prefixEnd_1320604 : Nat := 4983230072969 + 3 ^ 40 * 1320604 * 2
def baseEnd_1320604 : Nat := 75344956250028484941851

theorem tailTrace_1320604 : CollatzResearch.WordTrace tailWord_1320604 prefixEnd_1320604 75344956250028484941851 := by
  unfold tailWord_1320604
  simp only [CollatzResearch.WordTrace]
  refine ⟨24083192453842362026028433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32110923271789816034704577 24083192453842362026028433)
  ·
    refine ⟨18062394340381771519521325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24083192453842362026028433 18062394340381771519521325)
    ·
      refine ⟨6773397877643164319820497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18062394340381771519521325 6773397877643164319820497)
      ·
        refine ⟨5080048408232373239865373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6773397877643164319820497 5080048408232373239865373)
        ·
          refine ⟨1905018153087139964949515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5080048408232373239865373 1905018153087139964949515)
          ·
            refine ⟨2857527229630709947424273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905018153087139964949515 2857527229630709947424273)
            ·
              refine ⟨2143145422223032460568205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2857527229630709947424273 2143145422223032460568205)
              ·
                refine ⟨803679533333637172713077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143145422223032460568205 803679533333637172713077)
                ·
                  refine ⟨75344956250028484941851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 803679533333637172713077 75344956250028484941851)
                  ·
                    rfl

theorem cell23_1320604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_1320604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320604 prefixEnd_1320604 := by exact prefixLift 1320604
  have htrace : WordTrace (prefixWord ++ tailWord_1320604) baseStart_1320604 baseEnd_1320604 := by
    simpa [prefixWord, tailWord_1320604, baseEnd_1320604] using wordTrace_append hprefix tailTrace_1320604
  have hstable : (prefixWord ++ tailWord_1320604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320604).length < 2 ^ (prefixWord ++ tailWord_1320604).sum := by decide
  have hdescent : baseEnd_1320604 < baseStart_1320604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320637 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_1320637 : Nat := 118140960795 + 1320637 * 2 ^ 59
def prefixEnd_1320637 : Nat := 4983230072969 + 3 ^ 40 * 1320637 * 2
def baseEnd_1320637 : Nat := 678121551111854735364007

theorem tailTrace_1320637 : CollatzResearch.WordTrace tailWord_1320637 prefixEnd_1320637 678121551111854735364007 := by
  unfold tailWord_1320637
  simp only [CollatzResearch.WordTrace]
  refine ⟨48167588516565170688008165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32111725677710113792005443 48167588516565170688008165)
  ·
    refine ⟨9031422846855969504001531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48167588516565170688008165 9031422846855969504001531)
    ·
      refine ⟨13547134270283954256002297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9031422846855969504001531 13547134270283954256002297)
      ·
        refine ⟨10160350702712965692001723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13547134270283954256002297 10160350702712965692001723)
        ·
          refine ⟨15240526054069448538002585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10160350702712965692001723 15240526054069448538002585)
          ·
            refine ⟨11430394540552086403501939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15240526054069448538002585 11430394540552086403501939)
            ·
              refine ⟨17145591810828129605252909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430394540552086403501939 17145591810828129605252909)
              ·
                refine ⟨6429596929060548601969841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17145591810828129605252909 6429596929060548601969841)
                ·
                  refine ⟨4822197696795411451477381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6429596929060548601969841 4822197696795411451477381)
                  ·
                    refine ⟨904162068149139647152009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822197696795411451477381 904162068149139647152009)
                    ·
                      refine ⟨678121551111854735364007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904162068149139647152009 678121551111854735364007)
                      ·
                        rfl

theorem cell23_1320637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_1320637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320637 prefixEnd_1320637 := by exact prefixLift 1320637
  have htrace : WordTrace (prefixWord ++ tailWord_1320637) baseStart_1320637 baseEnd_1320637 := by
    simpa [prefixWord, tailWord_1320637, baseEnd_1320637] using wordTrace_append hprefix tailTrace_1320637
  have hstable : (prefixWord ++ tailWord_1320637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320637).length < 2 ^ (prefixWord ++ tailWord_1320637).sum := by decide
  have hdescent : baseEnd_1320637 < baseStart_1320637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320640 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_1320640 : Nat := 118140960795 + 1320640 * 2 ^ 59
def prefixEnd_1320640 : Nat := 4983230072969 + 3 ^ 40 * 1320640 * 2
def baseEnd_1320640 : Nat := 678123091553818223626493

theorem tailTrace_1320640 : CollatzResearch.WordTrace tailWord_1320640 prefixEnd_1320640 678123091553818223626493 := by
  unfold tailWord_1320640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24083848967777151100183687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32111798623702868133578249 24083848967777151100183687)
  ·
    refine ⟨36125773451665726650275531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24083848967777151100183687 36125773451665726650275531)
    ·
      refine ⟨54188660177498589975413297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36125773451665726650275531 54188660177498589975413297)
      ·
        refine ⟨40641495133123942481559973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54188660177498589975413297 40641495133123942481559973)
        ·
          refine ⟨7620280337460739215292495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40641495133123942481559973 7620280337460739215292495)
          ·
            refine ⟨11430420506191108822938743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620280337460739215292495 11430420506191108822938743)
            ·
              refine ⟨17145630759286663234408115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430420506191108822938743 17145630759286663234408115)
              ·
                refine ⟨25718446138929994851612173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17145630759286663234408115 25718446138929994851612173)
                ·
                  refine ⟨9644417302098748069354565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25718446138929994851612173 9644417302098748069354565)
                  ·
                    refine ⟨1808328244143515263003981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9644417302098748069354565 1808328244143515263003981)
                    ·
                      refine ⟨678123091553818223626493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808328244143515263003981 678123091553818223626493)
                      ·
                        rfl

theorem cell23_1320640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_1320640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320640 prefixEnd_1320640 := by exact prefixLift 1320640
  have htrace : WordTrace (prefixWord ++ tailWord_1320640) baseStart_1320640 baseEnd_1320640 := by
    simpa [prefixWord, tailWord_1320640, baseEnd_1320640] using wordTrace_append hprefix tailTrace_1320640
  have hstable : (prefixWord ++ tailWord_1320640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320640).length < 2 ^ (prefixWord ++ tailWord_1320640).sum := by decide
  have hdescent : baseEnd_1320640 < baseStart_1320640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320694 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_1320694 : Nat := 118140960795 + 1320694 * 2 ^ 59
def prefixEnd_1320694 : Nat := 4983230072969 + 3 ^ 40 * 1320694 * 2
def baseEnd_1320694 : Nat := 75350091056573445816805

theorem tailTrace_1320694 : CollatzResearch.WordTrace tailWord_1320694 prefixEnd_1320694 75350091056573445816805 := by
  unfold tailWord_1320694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010604217334916838927071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32113111651572446281888757 3010604217334916838927071)
  ·
    refine ⟨4515906326002375258390607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010604217334916838927071 4515906326002375258390607)
    ·
      refine ⟨6773859489003562887585911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515906326002375258390607 6773859489003562887585911)
      ·
        refine ⟨10160789233505344331378867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773859489003562887585911 10160789233505344331378867)
        ·
          refine ⟨15241183850258016497068301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10160789233505344331378867 15241183850258016497068301)
          ·
            refine ⟨5715443943846756186400613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15241183850258016497068301 5715443943846756186400613)
            ·
              refine ⟨1071645739471266784950115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5715443943846756186400613 1071645739471266784950115)
              ·
                refine ⟨1607468609206900177425173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071645739471266784950115 1607468609206900177425173)
                ·
                  refine ⟨75350091056573445816805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1607468609206900177425173 75350091056573445816805)
                  ·
                    rfl

theorem cell23_1320694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_1320694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320694 prefixEnd_1320694 := by exact prefixLift 1320694
  have htrace : WordTrace (prefixWord ++ tailWord_1320694) baseStart_1320694 baseEnd_1320694 := by
    simpa [prefixWord, tailWord_1320694, baseEnd_1320694] using wordTrace_append hprefix tailTrace_1320694
  have hstable : (prefixWord ++ tailWord_1320694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320694).length < 2 ^ (prefixWord ++ tailWord_1320694).sum := by decide
  have hdescent : baseEnd_1320694 < baseStart_1320694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320707 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 1, 5]
def baseStart_1320707 : Nat := 118140960795 + 1320707 * 2 ^ 59
def prefixEnd_1320707 : Nat := 4983230072969 + 3 ^ 40 * 1320707 * 2
def baseEnd_1320707 : Nat := 226052498252556487162895

theorem tailTrace_1320707 : CollatzResearch.WordTrace tailWord_1320707 prefixEnd_1320707 226052498252556487162895 := by
  unfold tailWord_1320707
  simp only [CollatzResearch.WordTrace]
  refine ⟨48170141626311572643056375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32113427750874381762037583 48170141626311572643056375)
  ·
    refine ⟨72255212439467358964584563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48170141626311572643056375 72255212439467358964584563)
    ·
      refine ⟨108382818659201038446876845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72255212439467358964584563 108382818659201038446876845)
      ·
        refine ⟨40643556997200389417578817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108382818659201038446876845 40643556997200389417578817)
        ·
          refine ⟨30482667747900292063184113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40643556997200389417578817 30482667747900292063184113)
          ·
            refine ⟨22862000810925219047388085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30482667747900292063184113 22862000810925219047388085)
            ·
              refine ⟨2143312576024239285692633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22862000810925219047388085 2143312576024239285692633)
              ·
                refine ⟨1607484432018179464269475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143312576024239285692633 1607484432018179464269475)
                ·
                  refine ⟨2411226648027269196404213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607484432018179464269475 2411226648027269196404213)
                  ·
                    refine ⟨226052498252556487162895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2411226648027269196404213 226052498252556487162895)
                    ·
                      rfl

theorem cell23_1320707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 5].length) (baseStart_1320707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320707 prefixEnd_1320707 := by exact prefixLift 1320707
  have htrace : WordTrace (prefixWord ++ tailWord_1320707) baseStart_1320707 baseEnd_1320707 := by
    simpa [prefixWord, tailWord_1320707, baseEnd_1320707] using wordTrace_append hprefix tailTrace_1320707
  have hstable : (prefixWord ++ tailWord_1320707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320707).length < 2 ^ (prefixWord ++ tailWord_1320707).sum := by decide
  have hdescent : baseEnd_1320707 < baseStart_1320707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320714 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_1320714 : Nat := 118140960795 + 1320714 * 2 ^ 59
def prefixEnd_1320714 : Nat := 4983230072969 + 3 ^ 40 * 1320714 * 2
def baseEnd_1320714 : Nat := 678161089122250934101153

theorem tailTrace_1320714 : CollatzResearch.WordTrace tailWord_1320714 prefixEnd_1320714 678161089122250934101153 := by
  unfold tailWord_1320714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12042599234321553209640299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32113597958190808559040797 12042599234321553209640299)
  ·
    refine ⟨18063898851482329814460449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12042599234321553209640299 18063898851482329814460449)
    ·
      refine ⟨13547924138611747360845337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18063898851482329814460449 13547924138611747360845337)
      ·
        refine ⟨10160943103958810520634003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13547924138611747360845337 10160943103958810520634003)
        ·
          refine ⟨15241414655938215780951005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10160943103958810520634003 15241414655938215780951005)
          ·
            refine ⟨5715530495976830917856627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15241414655938215780951005 5715530495976830917856627)
            ·
              refine ⟨8573295743965246376784941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715530495976830917856627 8573295743965246376784941)
              ·
                refine ⟨3214985903986967391294353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8573295743965246376784941 3214985903986967391294353)
                ·
                  refine ⟨2411239427990225543470765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214985903986967391294353 2411239427990225543470765)
                  ·
                    refine ⟨904214785496334578801537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411239427990225543470765 904214785496334578801537)
                    ·
                      refine ⟨678161089122250934101153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904214785496334578801537 678161089122250934101153)
                      ·
                        rfl

theorem cell23_1320714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_1320714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320714 prefixEnd_1320714 := by exact prefixLift 1320714
  have htrace : WordTrace (prefixWord ++ tailWord_1320714) baseStart_1320714 baseEnd_1320714 := by
    simpa [prefixWord, tailWord_1320714, baseEnd_1320714] using wordTrace_append hprefix tailTrace_1320714
  have hstable : (prefixWord ++ tailWord_1320714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320714).length < 2 ^ (prefixWord ++ tailWord_1320714).sum := by decide
  have hdescent : baseEnd_1320714 < baseStart_1320714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320754 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_1320754 : Nat := 118140960795 + 1320754 * 2 ^ 59
def prefixEnd_1320754 : Nat := 4983230072969 + 3 ^ 40 * 1320754 * 2
def baseEnd_1320754 : Nat := 226060542782810259200323

theorem tailTrace_1320754 : CollatzResearch.WordTrace tailWord_1320754 prefixEnd_1320754 226060542782810259200323 := by
  unfold tailWord_1320754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12042963964285324917504329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32114570571427533113344877 12042963964285324917504329)
  ·
    refine ⟨9032222973213993688128247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12042963964285324917504329 9032222973213993688128247)
    ·
      refine ⟨13548334459820990532192371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9032222973213993688128247 13548334459820990532192371)
      ·
        refine ⟨20322501689731485798288557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13548334459820990532192371 20322501689731485798288557)
        ·
          refine ⟨7620938133649307174358209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20322501689731485798288557 7620938133649307174358209)
          ·
            refine ⟨5715703600236980380768657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7620938133649307174358209 5715703600236980380768657)
            ·
              refine ⟨4286777700177735285576493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5715703600236980380768657 4286777700177735285576493)
              ·
                refine ⟨1607541637566650732091185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4286777700177735285576493 1607541637566650732091185)
                ·
                  refine ⟨1205656228174988049068389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1607541637566650732091185 1205656228174988049068389)
                  ·
                    refine ⟨226060542782810259200323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205656228174988049068389 226060542782810259200323)
                    ·
                      rfl

theorem cell23_1320754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_1320754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320754 prefixEnd_1320754 := by exact prefixLift 1320754
  have htrace : WordTrace (prefixWord ++ tailWord_1320754) baseStart_1320754 baseEnd_1320754 := by
    simpa [prefixWord, tailWord_1320754, baseEnd_1320754] using wordTrace_append hprefix tailTrace_1320754
  have hstable : (prefixWord ++ tailWord_1320754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320754).length < 2 ^ (prefixWord ++ tailWord_1320754).sum := by decide
  have hdescent : baseEnd_1320754 < baseStart_1320754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320777 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_1320777 : Nat := 118140960795 + 1320777 * 2 ^ 59
def prefixEnd_1320777 : Nat := 4983230072969 + 3 ^ 40 * 1320777 * 2
def baseEnd_1320777 : Nat := 678193438403484187613363

theorem tailTrace_1320777 : CollatzResearch.WordTrace tailWord_1320777 prefixEnd_1320777 678193438403484187613363 := by
  unfold tailWord_1320777
  simp only [CollatzResearch.WordTrace]
  refine ⟨48172694736057974598104585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32115129824038649732069723 48172694736057974598104585)
  ·
    refine ⟨36129521052043480948578439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48172694736057974598104585 36129521052043480948578439)
    ·
      refine ⟨54194281578065221422867659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36129521052043480948578439 54194281578065221422867659)
      ·
        refine ⟨81291422367097832134301489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54194281578065221422867659 81291422367097832134301489)
        ·
          refine ⟨60968566775323374100726117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81291422367097832134301489 60968566775323374100726117)
          ·
            refine ⟨11431606270373132643886147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60968566775323374100726117 11431606270373132643886147)
            ·
              refine ⟨17147409405559698965829221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11431606270373132643886147 17147409405559698965829221)
              ·
                refine ⟨3215139263542443556092979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17147409405559698965829221 3215139263542443556092979)
                ·
                  refine ⟨4822708895313665334139469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215139263542443556092979 4822708895313665334139469)
                  ·
                    refine ⟨1808515835742624500302301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4822708895313665334139469 1808515835742624500302301)
                    ·
                      refine ⟨678193438403484187613363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808515835742624500302301 678193438403484187613363)
                      ·
                        rfl

theorem cell23_1320777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_1320777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320777 prefixEnd_1320777 := by exact prefixLift 1320777
  have htrace : WordTrace (prefixWord ++ tailWord_1320777) baseStart_1320777 baseEnd_1320777 := by
    simpa [prefixWord, tailWord_1320777, baseEnd_1320777] using wordTrace_append hprefix tailTrace_1320777
  have hstable : (prefixWord ++ tailWord_1320777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320777).length < 2 ^ (prefixWord ++ tailWord_1320777).sum := by decide
  have hdescent : baseEnd_1320777 < baseStart_1320777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320778 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_1320778 : Nat := 118140960795 + 1320778 * 2 ^ 59
def prefixEnd_1320778 : Nat := 4983230072969 + 3 ^ 40 * 1320778 * 2
def baseEnd_1320778 : Nat := 678193951884138683700859

theorem tailTrace_1320778 : CollatzResearch.WordTrace tailWord_1320778 prefixEnd_1320778 678193951884138683700859 := by
  unfold tailWord_1320778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043182802263587942222747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32115154139369567845927325 12043182802263587942222747)
  ·
    refine ⟨18064774203395381913334121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12043182802263587942222747 18064774203395381913334121)
    ·
      refine ⟨13548580652546536435000591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18064774203395381913334121 13548580652546536435000591)
      ·
        refine ⟨20322870978819804652500887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13548580652546536435000591 20322870978819804652500887)
        ·
          refine ⟨30484306468229706978751331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20322870978819804652500887 30484306468229706978751331)
          ·
            refine ⟨45726459702344560468126997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30484306468229706978751331 45726459702344560468126997)
            ·
              refine ⟨2143427798547401271943453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45726459702344560468126997 2143427798547401271943453)
              ·
                refine ⟨803785424455275476978795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143427798547401271943453 803785424455275476978795)
                ·
                  refine ⟨1205678136682913215468193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803785424455275476978795 1205678136682913215468193)
                  ·
                    refine ⟨904258602512184911601145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205678136682913215468193 904258602512184911601145)
                    ·
                      refine ⟨678193951884138683700859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904258602512184911601145 678193951884138683700859)
                      ·
                        rfl

theorem cell23_1320778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_1320778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320778 prefixEnd_1320778 := by exact prefixLift 1320778
  have htrace : WordTrace (prefixWord ++ tailWord_1320778) baseStart_1320778 baseEnd_1320778 := by
    simpa [prefixWord, tailWord_1320778, baseEnd_1320778] using wordTrace_append hprefix tailTrace_1320778
  have hstable : (prefixWord ++ tailWord_1320778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320778).length < 2 ^ (prefixWord ++ tailWord_1320778).sum := by decide
  have hdescent : baseEnd_1320778 < baseStart_1320778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320794 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_1320794 : Nat := 118140960795 + 1320794 * 2 ^ 59
def prefixEnd_1320794 : Nat := 4983230072969 + 3 ^ 40 * 1320794 * 2
def baseEnd_1320794 : Nat := 678202167574610621100785

theorem tailTrace_1320794 : CollatzResearch.WordTrace tailWord_1320794 prefixEnd_1320794 678202167574610621100785 := by
  unfold tailWord_1320794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043328694249096625368359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32115543184664257667648957 12043328694249096625368359)
  ·
    refine ⟨18064993041373644938052539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12043328694249096625368359 18064993041373644938052539)
    ·
      refine ⟨27097489562060467407078809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18064993041373644938052539 27097489562060467407078809)
      ·
        refine ⟨20323117171545350555309107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27097489562060467407078809 20323117171545350555309107)
        ·
          refine ⟨30484675757318025832963661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20323117171545350555309107 30484675757318025832963661)
          ·
            refine ⟨11431753408994259687361373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30484675757318025832963661 11431753408994259687361373)
            ·
              refine ⟨4286907528372847382760515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11431753408994259687361373 4286907528372847382760515)
              ·
                refine ⟨6430361292559271074140773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286907528372847382760515 6430361292559271074140773)
                ·
                  refine ⟨1205692742354863326401395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6430361292559271074140773 1205692742354863326401395)
                  ·
                    refine ⟨1808539113532294989602093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205692742354863326401395 1808539113532294989602093)
                    ·
                      refine ⟨678202167574610621100785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808539113532294989602093 678202167574610621100785)
                      ·
                        rfl

theorem cell23_1320794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_1320794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320794 prefixEnd_1320794 := by exact prefixLift 1320794
  have htrace : WordTrace (prefixWord ++ tailWord_1320794) baseStart_1320794 baseEnd_1320794 := by
    simpa [prefixWord, tailWord_1320794, baseEnd_1320794] using wordTrace_append hprefix tailTrace_1320794
  have hstable : (prefixWord ++ tailWord_1320794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320794).length < 2 ^ (prefixWord ++ tailWord_1320794).sum := by decide
  have hdescent : baseEnd_1320794 < baseStart_1320794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320837 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_1320837 : Nat := 118140960795 + 1320837 * 2 ^ 59
def prefixEnd_1320837 : Nat := 4983230072969 + 3 ^ 40 * 1320837 * 2
def baseEnd_1320837 : Nat := 678224247242753952863087

theorem tailTrace_1320837 : CollatzResearch.WordTrace tailWord_1320837 prefixEnd_1320837 678224247242753952863087 := by
  unfold tailWord_1320837
  simp only [CollatzResearch.WordTrace]
  refine ⟨48174883115840604845288765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32116588743893736563525843 48174883115840604845288765)
  ·
    refine ⟨18065581168440226816983287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48174883115840604845288765 18065581168440226816983287)
    ·
      refine ⟨27098371752660340225474931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18065581168440226816983287 27098371752660340225474931)
      ·
        refine ⟨40647557628990510338212397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27098371752660340225474931 40647557628990510338212397)
        ·
          refine ⟨15242834110871441376829649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40647557628990510338212397 15242834110871441376829649)
          ·
            refine ⟨11432125583153581032622237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15242834110871441376829649 11432125583153581032622237)
            ·
              refine ⟨4287047093682592887233339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11432125583153581032622237 4287047093682592887233339)
              ·
                refine ⟨6430570640523889330850009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287047093682592887233339 6430570640523889330850009)
                ·
                  refine ⟨4822927980392916998137507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430570640523889330850009 4822927980392916998137507)
                  ·
                    refine ⟨7234391970589375497206261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4822927980392916998137507 7234391970589375497206261)
                    ·
                      refine ⟨678224247242753952863087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7234391970589375497206261 678224247242753952863087)
                      ·
                        rfl

theorem cell23_1320837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_1320837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320837 prefixEnd_1320837 := by exact prefixLift 1320837
  have htrace : WordTrace (prefixWord ++ tailWord_1320837) baseStart_1320837 baseEnd_1320837 := by
    simpa [prefixWord, tailWord_1320837, baseEnd_1320837] using wordTrace_append hprefix tailTrace_1320837
  have hstable : (prefixWord ++ tailWord_1320837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320837).length < 2 ^ (prefixWord ++ tailWord_1320837).sum := by decide
  have hdescent : baseEnd_1320837 < baseStart_1320837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320857 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 7]
def baseStart_1320857 : Nat := 118140960795 + 1320857 * 2 ^ 59
def prefixEnd_1320857 : Nat := 4983230072969 + 3 ^ 40 * 1320857 * 2
def baseEnd_1320857 : Nat := 75359390761760430512555

theorem tailTrace_1320857 : CollatzResearch.WordTrace tailWord_1320857 prefixEnd_1320857 75359390761760430512555 := by
  unfold tailWord_1320857
  simp only [CollatzResearch.WordTrace]
  refine ⟨48175612575768148261016825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32117075050512098840677883 48175612575768148261016825)
  ·
    refine ⟨36131709431826111195762619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48175612575768148261016825 36131709431826111195762619)
    ·
      refine ⟨54197564147739166793643929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36131709431826111195762619 54197564147739166793643929)
      ·
        refine ⟨40648173110804375095232947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54197564147739166793643929 40648173110804375095232947)
        ·
          refine ⟨60972259666206562642849421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40648173110804375095232947 60972259666206562642849421)
          ·
            refine ⟨22864597374827460991068533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60972259666206562642849421 22864597374827460991068533)
            ·
              refine ⟨2143556003890074467912675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22864597374827460991068533 2143556003890074467912675)
              ·
                refine ⟨3215334005835111701869013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143556003890074467912675 3215334005835111701869013)
                ·
                  refine ⟨75359390761760430512555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3215334005835111701869013 75359390761760430512555)
                  ·
                    rfl

theorem cell23_1320857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_1320857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320857 prefixEnd_1320857 := by exact prefixLift 1320857
  have htrace : WordTrace (prefixWord ++ tailWord_1320857) baseStart_1320857 baseEnd_1320857 := by
    simpa [prefixWord, tailWord_1320857, baseEnd_1320857] using wordTrace_append hprefix tailTrace_1320857
  have hstable : (prefixWord ++ tailWord_1320857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320857).length < 2 ^ (prefixWord ++ tailWord_1320857).sum := by decide
  have hdescent : baseEnd_1320857 < baseStart_1320857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320867 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 3]
def baseStart_1320867 : Nat := 118140960795 + 1320867 * 2 ^ 59
def prefixEnd_1320867 : Nat := 4983230072969 + 3 ^ 40 * 1320867 * 2
def baseEnd_1320867 : Nat := 678239651662388835487949

theorem tailTrace_1320867 : CollatzResearch.WordTrace tailWord_1320867 prefixEnd_1320867 678239651662388835487949 := by
  unfold tailWord_1320867
  simp only [CollatzResearch.WordTrace]
  refine ⟨48175977305731919968880855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32117318203821279979253903 48175977305731919968880855)
  ·
    refine ⟨72263965958597879953321283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48175977305731919968880855 72263965958597879953321283)
    ·
      refine ⟨108395948937896819929981925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72263965958597879953321283 108395948937896819929981925)
      ·
        refine ⟨20324240425855653736871611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108395948937896819929981925 20324240425855653736871611)
        ·
          refine ⟨30486360638783480605307417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20324240425855653736871611 30486360638783480605307417)
          ·
            refine ⟨22864770479087610453980563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30486360638783480605307417 22864770479087610453980563)
            ·
              refine ⟨34297155718631415680970845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22864770479087610453980563 34297155718631415680970845)
              ·
                refine ⟨12861433394486780880364067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34297155718631415680970845 12861433394486780880364067)
                ·
                  refine ⟨19292150091730171320546101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12861433394486780880364067 19292150091730171320546101)
                  ·
                    refine ⟨1808639071099703561301197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19292150091730171320546101 1808639071099703561301197)
                    ·
                      refine ⟨678239651662388835487949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808639071099703561301197 678239651662388835487949)
                      ·
                        rfl

theorem cell23_1320867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_1320867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320867 prefixEnd_1320867 := by exact prefixLift 1320867
  have htrace : WordTrace (prefixWord ++ tailWord_1320867) baseStart_1320867 baseEnd_1320867 := by
    simpa [prefixWord, tailWord_1320867, baseEnd_1320867] using wordTrace_append hprefix tailTrace_1320867
  have hstable : (prefixWord ++ tailWord_1320867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320867).length < 2 ^ (prefixWord ++ tailWord_1320867).sum := by decide
  have hdescent : baseEnd_1320867 < baseStart_1320867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320868 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_1320868 : Nat := 118140960795 + 1320868 * 2 ^ 59
def prefixEnd_1320868 : Nat := 4983230072969 + 3 ^ 40 * 1320868 * 2
def baseEnd_1320868 : Nat := 678240165143043331575445

theorem tailTrace_1320868 : CollatzResearch.WordTrace tailWord_1320868 prefixEnd_1320868 678240165143043331575445 := by
  unfold tailWord_1320868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24088006889364148569833629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32117342519152198093111505 24088006889364148569833629)
  ·
    refine ⟨9033002583511555713687611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24088006889364148569833629 9033002583511555713687611)
    ·
      refine ⟨13549503875267333570531417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9033002583511555713687611 13549503875267333570531417)
      ·
        refine ⟨10162127906450500177898563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13549503875267333570531417 10162127906450500177898563)
        ·
          refine ⟨15243191859675750266847845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10162127906450500177898563 15243191859675750266847845)
          ·
            refine ⟨2858098473689203175033971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15243191859675750266847845 2858098473689203175033971)
            ·
              refine ⟨4287147710533804762550957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858098473689203175033971 4287147710533804762550957)
              ·
                refine ⟨1607680391450176785956609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4287147710533804762550957 1607680391450176785956609)
                ·
                  refine ⟨1205760293587632589467457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1607680391450176785956609 1205760293587632589467457)
                  ·
                    refine ⟨904320220190724442100593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205760293587632589467457 904320220190724442100593)
                    ·
                      refine ⟨678240165143043331575445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904320220190724442100593 678240165143043331575445)
                      ·
                        rfl

theorem cell23_1320868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_1320868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320868 prefixEnd_1320868 := by exact prefixLift 1320868
  have htrace : WordTrace (prefixWord ++ tailWord_1320868) baseStart_1320868 baseEnd_1320868 := by
    simpa [prefixWord, tailWord_1320868, baseEnd_1320868] using wordTrace_append hprefix tailTrace_1320868
  have hstable : (prefixWord ++ tailWord_1320868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320868).length < 2 ^ (prefixWord ++ tailWord_1320868).sum := by decide
  have hdescent : baseEnd_1320868 < baseStart_1320868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320872 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1320872 : Nat := 118140960795 + 1320872 * 2 ^ 59
def prefixEnd_1320872 : Nat := 4983230072969 + 3 ^ 40 * 1320872 * 2
def baseEnd_1320872 : Nat := 678242219065661315925427

theorem tailTrace_1320872 : CollatzResearch.WordTrace tailWord_1320872 prefixEnd_1320872 678242219065661315925427 := by
  unfold tailWord_1320872
  simp only [CollatzResearch.WordTrace]
  refine ⟨24088079835356902911406435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32117439780475870548541913 24088079835356902911406435)
  ·
    refine ⟨36132119753035354367109653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24088079835356902911406435 36132119753035354367109653)
    ·
      refine ⟨1693693113423532235958265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36132119753035354367109653 1693693113423532235958265)
      ·
        refine ⟨1270269835067649176968699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1693693113423532235958265 1270269835067649176968699)
        ·
          refine ⟨1905404752601473765453049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270269835067649176968699 1905404752601473765453049)
          ·
            refine ⟨1429053564451105324089787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905404752601473765453049 1429053564451105324089787)
            ·
              refine ⟨2143580346676657986134681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429053564451105324089787 2143580346676657986134681)
              ·
                refine ⟨1607685260007493489601011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143580346676657986134681 1607685260007493489601011)
                ·
                  refine ⟨2411527890011240234401517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607685260007493489601011 2411527890011240234401517)
                  ·
                    refine ⟨904322958754215087900569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411527890011240234401517 904322958754215087900569)
                    ·
                      refine ⟨678242219065661315925427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904322958754215087900569 678242219065661315925427)
                      ·
                        rfl

theorem cell23_1320872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1320872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320872 prefixEnd_1320872 := by exact prefixLift 1320872
  have htrace : WordTrace (prefixWord ++ tailWord_1320872) baseStart_1320872 baseEnd_1320872 := by
    simpa [prefixWord, tailWord_1320872, baseEnd_1320872] using wordTrace_append hprefix tailTrace_1320872
  have hstable : (prefixWord ++ tailWord_1320872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320872).length < 2 ^ (prefixWord ++ tailWord_1320872).sum := by decide
  have hdescent : baseEnd_1320872 < baseStart_1320872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320904 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1320904 : Nat := 118140960795 + 1320904 * 2 ^ 59
def prefixEnd_1320904 : Nat := 4983230072969 + 3 ^ 40 * 1320904 * 2
def baseEnd_1320904 : Nat := 226086216815535063575093

theorem tailTrace_1320904 : CollatzResearch.WordTrace tailWord_1320904 prefixEnd_1320904 226086216815535063575093 := by
  unfold tailWord_1320904
  simp only [CollatzResearch.WordTrace]
  refine ⟨24088663403298937643988883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32118217871065250191985177 24088663403298937643988883)
  ·
    refine ⟨36132995104948406465983325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24088663403298937643988883 36132995104948406465983325)
    ·
      refine ⟨13549873164355652424743747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36132995104948406465983325 13549873164355652424743747)
      ·
        refine ⟨20324809746533478637115621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13549873164355652424743747 20324809746533478637115621)
        ·
          refine ⟨3810901827475027244459179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20324809746533478637115621 3810901827475027244459179)
          ·
            refine ⟨5716352741212540866688769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810901827475027244459179 5716352741212540866688769)
            ·
              refine ⟨4287264555909405650016577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5716352741212540866688769 4287264555909405650016577)
              ·
                refine ⟨3215448416932054237512433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287264555909405650016577 3215448416932054237512433)
                ·
                  refine ⟨2411586312699040678134325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3215448416932054237512433 2411586312699040678134325)
                  ·
                    refine ⟨226086216815535063575093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2411586312699040678134325 226086216815535063575093)
                    ·
                      rfl

theorem cell23_1320904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1320904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320904 prefixEnd_1320904 := by exact prefixLift 1320904
  have htrace : WordTrace (prefixWord ++ tailWord_1320904) baseStart_1320904 baseEnd_1320904 := by
    simpa [prefixWord, tailWord_1320904, baseEnd_1320904] using wordTrace_append hprefix tailTrace_1320904
  have hstable : (prefixWord ++ tailWord_1320904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320904).length < 2 ^ (prefixWord ++ tailWord_1320904).sum := by decide
  have hdescent : baseEnd_1320904 < baseStart_1320904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320908 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 5]
def baseStart_1320908 : Nat := 118140960795 + 1320908 * 2 ^ 59
def prefixEnd_1320908 : Nat := 4983230072969 + 3 ^ 40 * 1320908 * 2
def baseEnd_1320908 : Nat := 75362300485469241675029

theorem tailTrace_1320908 : CollatzResearch.WordTrace tailWord_1320908 prefixEnd_1320908 75362300485469241675029 := by
  unfold tailWord_1320908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24088736349291691985561689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32118315132388922647415585 24088736349291691985561689)
  ·
    refine ⟨18066552261968768989171267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24088736349291691985561689 18066552261968768989171267)
    ·
      refine ⟨27099828392953153483756901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18066552261968768989171267 27099828392953153483756901)
      ·
        refine ⟨5081217823678716278204419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27099828392953153483756901 5081217823678716278204419)
        ·
          refine ⟨7621826735518074417306629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081217823678716278204419 7621826735518074417306629)
          ·
            refine ⟨1429092512909638953244993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7621826735518074417306629 1429092512909638953244993)
            ·
              refine ⟨1071819384682229214933745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429092512909638953244993 1071819384682229214933745)
              ·
                refine ⟨803864538511671911200309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071819384682229214933745 803864538511671911200309)
                ·
                  refine ⟨75362300485469241675029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 803864538511671911200309 75362300485469241675029)
                  ·
                    rfl

theorem cell23_1320908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_1320908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320908 prefixEnd_1320908 := by exact prefixLift 1320908
  have htrace : WordTrace (prefixWord ++ tailWord_1320908) baseStart_1320908 baseEnd_1320908 := by
    simpa [prefixWord, tailWord_1320908, baseEnd_1320908] using wordTrace_append hprefix tailTrace_1320908
  have hstable : (prefixWord ++ tailWord_1320908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320908).length < 2 ^ (prefixWord ++ tailWord_1320908).sum := by decide
  have hdescent : baseEnd_1320908 < baseStart_1320908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320918 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1320918 : Nat := 118140960795 + 1320918 * 2 ^ 59
def prefixEnd_1320918 : Nat := 4983230072969 + 3 ^ 40 * 1320918 * 2
def baseEnd_1320918 : Nat := 678265839175768135950215

theorem tailTrace_1320918 : CollatzResearch.WordTrace tailWord_1320918 prefixEnd_1320918 678265839175768135950215 := by
  unfold tailWord_1320918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011114839284197229936713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32118558285698103785991605 3011114839284197229936713)
  ·
    refine ⟨2258336129463147922452535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3011114839284197229936713 2258336129463147922452535)
    ·
      refine ⟨3387504194194721883678803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258336129463147922452535 3387504194194721883678803)
      ·
        refine ⟨5081256291292082825518205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3387504194194721883678803 5081256291292082825518205)
        ·
          refine ⟨1905471109234531059569327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5081256291292082825518205 1905471109234531059569327)
          ·
            refine ⟨2858206663851796589353991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905471109234531059569327 2858206663851796589353991)
            ·
              refine ⟨4287309995777694884030987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858206663851796589353991 4287309995777694884030987)
              ·
                refine ⟨6430964993666542326046481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287309995777694884030987 6430964993666542326046481)
                ·
                  refine ⟨4823223745249906744534861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430964993666542326046481 4823223745249906744534861)
                  ·
                    refine ⟨1808708904468715029200573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4823223745249906744534861 1808708904468715029200573)
                    ·
                      refine ⟨678265839175768135950215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808708904468715029200573 678265839175768135950215)
                      ·
                        rfl

theorem cell23_1320918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1320918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320918 prefixEnd_1320918 := by exact prefixLift 1320918
  have htrace : WordTrace (prefixWord ++ tailWord_1320918) baseStart_1320918 baseEnd_1320918 := by
    simpa [prefixWord, tailWord_1320918, baseEnd_1320918] using wordTrace_append hprefix tailTrace_1320918
  have hstable : (prefixWord ++ tailWord_1320918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320918).length < 2 ^ (prefixWord ++ tailWord_1320918).sum := by decide
  have hdescent : baseEnd_1320918 < baseStart_1320918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320958 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1320958 : Nat := 118140960795 + 1320958 * 2 ^ 59
def prefixEnd_1320958 : Nat := 4983230072969 + 3 ^ 40 * 1320958 * 2
def baseEnd_1320958 : Nat := 678286378401947979450031

theorem tailTrace_1320958 : CollatzResearch.WordTrace tailWord_1320958 prefixEnd_1320958 678286378401947979450031 := by
  unfold tailWord_1320958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022412043550280313805441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32119530898934828340295685 6022412043550280313805441)
  ·
    refine ⟨4516809032662710235354081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6022412043550280313805441 4516809032662710235354081)
    ·
      refine ⟨3387606774497032676515561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4516809032662710235354081 3387606774497032676515561)
      ·
        refine ⟨2540705080872774507386671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3387606774497032676515561 2540705080872774507386671)
        ·
          refine ⟨3811057621309161761080007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540705080872774507386671 3811057621309161761080007)
          ·
            refine ⟨5716586431963742641620011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811057621309161761080007 5716586431963742641620011)
            ·
              refine ⟨8574879647945613962430017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716586431963742641620011 8574879647945613962430017)
              ·
                refine ⟨6431159735959210471822513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8574879647945613962430017 6431159735959210471822513)
                ·
                  refine ⟨4823369801969407853866885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6431159735959210471822513 4823369801969407853866885)
                  ·
                    refine ⟨904381837869263972600041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823369801969407853866885 904381837869263972600041)
                    ·
                      refine ⟨678286378401947979450031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904381837869263972600041 678286378401947979450031)
                      ·
                        rfl

theorem cell23_1320958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1320958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320958 prefixEnd_1320958 := by exact prefixLift 1320958
  have htrace : WordTrace (prefixWord ++ tailWord_1320958) baseStart_1320958 baseEnd_1320958 := by
    simpa [prefixWord, tailWord_1320958, baseEnd_1320958] using wordTrace_append hprefix tailTrace_1320958
  have hstable : (prefixWord ++ tailWord_1320958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320958).length < 2 ^ (prefixWord ++ tailWord_1320958).sum := by decide
  have hdescent : baseEnd_1320958 < baseStart_1320958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320991 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 3]
def baseStart_1320991 : Nat := 118140960795 + 1320991 * 2 ^ 59
def prefixEnd_1320991 : Nat := 4983230072969 + 3 ^ 40 * 1320991 * 2
def baseEnd_1320991 : Nat := 678303323263546350337379

theorem tailTrace_1320991 : CollatzResearch.WordTrace tailWord_1320991 prefixEnd_1320991 678303323263546350337379 := by
  unfold tailWord_1320991
  simp only [CollatzResearch.WordTrace]
  refine ⟨48180499957282689146394827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32120333304855126097596551 48180499957282689146394827)
  ·
    refine ⟨72270749935924033719592241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48180499957282689146394827 72270749935924033719592241)
    ·
      refine ⟨54203062451943025289694181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72270749935924033719592241 54203062451943025289694181)
      ·
        refine ⟨10163074209739317241817659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54203062451943025289694181 10163074209739317241817659)
        ·
          refine ⟨15244611314608975862726489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10163074209739317241817659 15244611314608975862726489)
          ·
            refine ⟨11433458485956731897044867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15244611314608975862726489 11433458485956731897044867)
            ·
              refine ⟨17150187728935097845567301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11433458485956731897044867 17150187728935097845567301)
              ·
                refine ⟨3215660199175330846043869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17150187728935097845567301 3215660199175330846043869)
                ·
                  refine ⟨1205872574690749067266451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3215660199175330846043869 1205872574690749067266451)
                  ·
                    refine ⟨1808808862036123600899677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205872574690749067266451 1808808862036123600899677)
                    ·
                      refine ⟨678303323263546350337379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808808862036123600899677 678303323263546350337379)
                      ·
                        rfl

theorem cell23_1320991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_1320991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1320991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1320991 prefixEnd_1320991 := by exact prefixLift 1320991
  have htrace : WordTrace (prefixWord ++ tailWord_1320991) baseStart_1320991 baseEnd_1320991 := by
    simpa [prefixWord, tailWord_1320991, baseEnd_1320991] using wordTrace_append hprefix tailTrace_1320991
  have hstable : (prefixWord ++ tailWord_1320991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320991).length < 2 ^ (prefixWord ++ tailWord_1320991).sum := by decide
  have hdescent : baseEnd_1320991 < baseStart_1320991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321025 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1321025 : Nat := 118140960795 + 1321025 * 2 ^ 59
def prefixEnd_1321025 : Nat := 4983230072969 + 3 ^ 40 * 1321025 * 2
def baseEnd_1321025 : Nat := 678320781605799217312223

theorem tailTrace_1321025 : CollatzResearch.WordTrace tailWord_1321025 prefixEnd_1321025 678320781605799217312223 := by
  unfold tailWord_1321025
  simp only [CollatzResearch.WordTrace]
  refine ⟨48181740039159512953132529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32121160026106341968755019 48181740039159512953132529)
  ·
    refine ⟨36136305029369634714849397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48181740039159512953132529 36136305029369634714849397)
    ·
      refine ⟨3387778596503403254517131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36136305029369634714849397 3387778596503403254517131)
      ·
        refine ⟨5081667894755104881775697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3387778596503403254517131 5081667894755104881775697)
        ·
          refine ⟨3811250921066328661331773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5081667894755104881775697 3811250921066328661331773)
          ·
            refine ⟨1429219095399873247999415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3811250921066328661331773 1429219095399873247999415)
            ·
              refine ⟨2143828643099809871999123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429219095399873247999415 2143828643099809871999123)
              ·
                refine ⟨3215742964649714807998685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143828643099809871999123 3215742964649714807998685)
                ·
                  refine ⟨1205903611743643052999507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3215742964649714807998685 1205903611743643052999507)
                  ·
                    refine ⟨1808855417615464579499261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205903611743643052999507 1808855417615464579499261)
                    ·
                      refine ⟨678320781605799217312223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808855417615464579499261 678320781605799217312223)
                      ·
                        rfl

theorem cell23_1321025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1321025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321025 prefixEnd_1321025 := by exact prefixLift 1321025
  have htrace : WordTrace (prefixWord ++ tailWord_1321025) baseStart_1321025 baseEnd_1321025 := by
    simpa [prefixWord, tailWord_1321025, baseEnd_1321025] using wordTrace_append hprefix tailTrace_1321025
  have hstable : (prefixWord ++ tailWord_1321025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321025).length < 2 ^ (prefixWord ++ tailWord_1321025).sum := by decide
  have hdescent : baseEnd_1321025 < baseStart_1321025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321034 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1321034 : Nat := 118140960795 + 1321034 * 2 ^ 59
def prefixEnd_1321034 : Nat := 4983230072969 + 3 ^ 40 * 1321034 * 2
def baseEnd_1321034 : Nat := 678325402931689682099681

theorem tailTrace_1321034 : CollatzResearch.WordTrace tailWord_1321034 prefixEnd_1321034 678325402931689682099681 := by
  unfold tailWord_1321034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12045517074031726872552539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32121378864084604993473437 12045517074031726872552539)
  ·
    refine ⟨18068275611047590308828809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12045517074031726872552539 18068275611047590308828809)
    ·
      refine ⟨13551206708285692731621607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18068275611047590308828809 13551206708285692731621607)
      ·
        refine ⟨20326810062428539097432411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13551206708285692731621607 20326810062428539097432411)
        ·
          refine ⟨30490215093642808646148617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20326810062428539097432411 30490215093642808646148617)
          ·
            refine ⟨22867661320232106484611463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30490215093642808646148617 22867661320232106484611463)
            ·
              refine ⟨34301491980348159726917195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22867661320232106484611463 34301491980348159726917195)
              ·
                refine ⟨51452237970522239590375793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34301491980348159726917195 51452237970522239590375793)
                ·
                  refine ⟨38589178477891679692781845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51452237970522239590375793 38589178477891679692781845)
                  ·
                    refine ⟨1808867741151172485599149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38589178477891679692781845 1808867741151172485599149)
                    ·
                      refine ⟨678325402931689682099681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808867741151172485599149 678325402931689682099681)
                      ·
                        rfl

theorem cell23_1321034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1321034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321034 prefixEnd_1321034 := by exact prefixLift 1321034
  have htrace : WordTrace (prefixWord ++ tailWord_1321034) baseStart_1321034 baseEnd_1321034 := by
    simpa [prefixWord, tailWord_1321034, baseEnd_1321034] using wordTrace_append hprefix tailTrace_1321034
  have hstable : (prefixWord ++ tailWord_1321034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321034).length < 2 ^ (prefixWord ++ tailWord_1321034).sum := by decide
  have hdescent : baseEnd_1321034 < baseStart_1321034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321048 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_1321048 : Nat := 118140960795 + 1321048 * 2 ^ 59
def prefixEnd_1321048 : Nat := 4983230072969 + 3 ^ 40 * 1321048 * 2
def baseEnd_1321048 : Nat := 678332591660852627324617

theorem tailTrace_1321048 : CollatzResearch.WordTrace tailWord_1321048 prefixEnd_1321048 678332591660852627324617 := by
  unfold tailWord_1321048
  simp only [CollatzResearch.WordTrace]
  refine ⟨24091289459038093940609899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32121719278717458587479865 24091289459038093940609899)
  ·
    refine ⟨36136934188557140910914849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24091289459038093940609899 36136934188557140910914849)
    ·
      refine ⟨27102700641417855683186137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36136934188557140910914849 27102700641417855683186137)
      ·
        refine ⟨20327025481063391762389603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27102700641417855683186137 20327025481063391762389603)
        ·
          refine ⟨30490538221595087643584405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20327025481063391762389603 30490538221595087643584405)
          ·
            refine ⟨1429243979137269733293019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30490538221595087643584405 1429243979137269733293019)
            ·
              refine ⟨2143865968705904599939529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429243979137269733293019 2143865968705904599939529)
              ·
                refine ⟨1607899476529428449954647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143865968705904599939529 1607899476529428449954647)
                ·
                  refine ⟨2411849214794142674931971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607899476529428449954647 2411849214794142674931971)
                  ·
                    refine ⟨3617773822191214012397957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2411849214794142674931971 3617773822191214012397957)
                    ·
                      refine ⟨678332591660852627324617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3617773822191214012397957 678332591660852627324617)
                      ·
                        rfl

theorem cell23_1321048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_1321048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321048 prefixEnd_1321048 := by exact prefixLift 1321048
  have htrace : WordTrace (prefixWord ++ tailWord_1321048) baseStart_1321048 baseEnd_1321048 := by
    simpa [prefixWord, tailWord_1321048, baseEnd_1321048] using wordTrace_append hprefix tailTrace_1321048
  have hstable : (prefixWord ++ tailWord_1321048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321048).length < 2 ^ (prefixWord ++ tailWord_1321048).sum := by decide
  have hdescent : baseEnd_1321048 < baseStart_1321048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321058 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1321058 : Nat := 118140960795 + 1321058 * 2 ^ 59
def prefixEnd_1321058 : Nat := 4983230072969 + 3 ^ 40 * 1321058 * 2
def baseEnd_1321058 : Nat := 226112575489132529399857

theorem tailTrace_1321058 : CollatzResearch.WordTrace tailWord_1321058 prefixEnd_1321058 226112575489132529399857 := by
  unfold tailWord_1321058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12045735912009989897270957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32121962432026639726055885 12045735912009989897270957)
  ·
    refine ⟨4517150967003746211476609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12045735912009989897270957 4517150967003746211476609)
    ·
      refine ⟨3387863225252809658607457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4517150967003746211476609 3387863225252809658607457)
      ·
        refine ⟨2540897418939607243955593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3387863225252809658607457 2540897418939607243955593)
        ·
          refine ⟨1905673064204705432966695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2540897418939607243955593 1905673064204705432966695)
          ·
            refine ⟨2858509596307058149450043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905673064204705432966695 2858509596307058149450043)
            ·
              refine ⟨4287764394460587224175065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858509596307058149450043 4287764394460587224175065)
              ·
                refine ⟨3215823295845440418131299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287764394460587224175065 3215823295845440418131299)
                ·
                  refine ⟨4823734943768160627196949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215823295845440418131299 4823734943768160627196949)
                  ·
                    refine ⟨226112575489132529399857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4823734943768160627196949 226112575489132529399857)
                    ·
                      rfl

theorem cell23_1321058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1321058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321058 prefixEnd_1321058 := by exact prefixLift 1321058
  have htrace : WordTrace (prefixWord ++ tailWord_1321058) baseStart_1321058 baseEnd_1321058 := by
    simpa [prefixWord, tailWord_1321058, baseEnd_1321058] using wordTrace_append hprefix tailTrace_1321058
  have hstable : (prefixWord ++ tailWord_1321058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321058).length < 2 ^ (prefixWord ++ tailWord_1321058).sum := by decide
  have hdescent : baseEnd_1321058 < baseStart_1321058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321061 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1321061 : Nat := 118140960795 + 1321061 * 2 ^ 59
def prefixEnd_1321061 : Nat := 4983230072969 + 3 ^ 40 * 1321061 * 2
def baseEnd_1321061 : Nat := 678339266909361076462057

theorem tailTrace_1321061 : CollatzResearch.WordTrace tailWord_1321061 prefixEnd_1321061 678339266909361076462057 := by
  unfold tailWord_1321061
  simp only [CollatzResearch.WordTrace]
  refine ⟨48183053067029091101443037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32122035378019394067628691 48183053067029091101443037)
  ·
    refine ⟨18068644900135909163041139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48183053067029091101443037 18068644900135909163041139)
    ·
      refine ⟨27102967350203863744561709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18068644900135909163041139 27102967350203863744561709)
      ·
        refine ⟨10163612756326448904210641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27102967350203863744561709 10163612756326448904210641)
        ·
          refine ⟨7622709567244836678157981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10163612756326448904210641 7622709567244836678157981)
          ·
            refine ⟨2858516087716813754309243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7622709567244836678157981 2858516087716813754309243)
            ·
              refine ⟨4287774131575220631463865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858516087716813754309243 4287774131575220631463865)
              ·
                refine ⟨3215830598681415473597899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287774131575220631463865 3215830598681415473597899)
                ·
                  refine ⟨4823745898022123210396849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215830598681415473597899 4823745898022123210396849)
                  ·
                    refine ⟨3617809423516592407797637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4823745898022123210396849 3617809423516592407797637)
                    ·
                      refine ⟨678339266909361076462057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3617809423516592407797637 678339266909361076462057)
                      ·
                        rfl

theorem cell23_1321061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1321061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321061 prefixEnd_1321061 := by exact prefixLift 1321061
  have htrace : WordTrace (prefixWord ++ tailWord_1321061) baseStart_1321061 baseEnd_1321061 := by
    simpa [prefixWord, tailWord_1321061, baseEnd_1321061] using wordTrace_append hprefix tailTrace_1321061
  have hstable : (prefixWord ++ tailWord_1321061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321061).length < 2 ^ (prefixWord ++ tailWord_1321061).sum := by decide
  have hdescent : baseEnd_1321061 < baseStart_1321061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321065 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 1, 2, 2]
def baseStart_1321065 : Nat := 118140960795 + 1321065 * 2 ^ 59
def prefixEnd_1321065 : Nat := 4983230072969 + 3 ^ 40 * 1321065 * 2
def baseEnd_1321065 : Nat := 678341320831979060812039

theorem tailTrace_1321065 : CollatzResearch.WordTrace tailWord_1321065 prefixEnd_1321065 678341320831979060812039 := by
  unfold tailWord_1321065
  simp only [CollatzResearch.WordTrace]
  refine ⟨48183198959014599784588649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32122132639343066523059099 48183198959014599784588649)
  ·
    refine ⟨36137399219260949838441487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48183198959014599784588649 36137399219260949838441487)
    ·
      refine ⟨54206098828891424757662231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36137399219260949838441487 54206098828891424757662231)
      ·
        refine ⟨81309148243337137136493347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54206098828891424757662231 81309148243337137136493347)
        ·
          refine ⟨121963722365005705704740021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81309148243337137136493347 121963722365005705704740021)
          ·
            refine ⟨11434098971719284909819377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121963722365005705704740021 11434098971719284909819377)
            ·
              refine ⟨8575574228789463682364533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11434098971719284909819377 8575574228789463682364533)
              ·
                refine ⟨803960083949012220221675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8575574228789463682364533 803960083949012220221675)
                ·
                  refine ⟨1205940125923518330332513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803960083949012220221675 1205940125923518330332513)
                  ·
                    refine ⟨904455094442638747749385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205940125923518330332513 904455094442638747749385)
                    ·
                      refine ⟨678341320831979060812039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904455094442638747749385 678341320831979060812039)
                      ·
                        rfl

theorem cell23_1321065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 2, 2].length) (baseStart_1321065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321065 prefixEnd_1321065 := by exact prefixLift 1321065
  have htrace : WordTrace (prefixWord ++ tailWord_1321065) baseStart_1321065 baseEnd_1321065 := by
    simpa [prefixWord, tailWord_1321065, baseEnd_1321065] using wordTrace_append hprefix tailTrace_1321065
  have hstable : (prefixWord ++ tailWord_1321065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321065).length < 2 ^ (prefixWord ++ tailWord_1321065).sum := by decide
  have hdescent : baseEnd_1321065 < baseStart_1321065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321084 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1321084 : Nat := 118140960795 + 1321084 * 2 ^ 59
def prefixEnd_1321084 : Nat := 4983230072969 + 3 ^ 40 * 1321084 * 2
def baseEnd_1321084 : Nat := 226117025654804828824817

theorem tailTrace_1321084 : CollatzResearch.WordTrace tailWord_1321084 prefixEnd_1321084 226117025654804828824817 := by
  unfold tailWord_1321084
  simp only [CollatzResearch.WordTrace]
  refine ⟨24091945972972883014765153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32122594630630510686353537 24091945972972883014765153)
  ·
    refine ⟨18068959479729662261073865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24091945972972883014765153 18068959479729662261073865)
    ·
      refine ⟨13551719609797246695805399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18068959479729662261073865 13551719609797246695805399)
      ·
        refine ⟨20327579414695870043708099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13551719609797246695805399 20327579414695870043708099)
        ·
          refine ⟨30491369122043805065562149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20327579414695870043708099 30491369122043805065562149)
          ·
            refine ⟨5717131710383213449792903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30491369122043805065562149 5717131710383213449792903)
            ·
              refine ⟨8575697565574820174689355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717131710383213449792903 8575697565574820174689355)
              ·
                refine ⟨12863546348362230262034033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8575697565574820174689355 12863546348362230262034033)
                ·
                  refine ⟨9647659761271672696525525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12863546348362230262034033 9647659761271672696525525)
                  ·
                    refine ⟨226117025654804828824817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9647659761271672696525525 226117025654804828824817)
                    ·
                      rfl

theorem cell23_1321084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1321084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321084 prefixEnd_1321084 := by exact prefixLift 1321084
  have htrace : WordTrace (prefixWord ++ tailWord_1321084) baseStart_1321084 baseEnd_1321084 := by
    simpa [prefixWord, tailWord_1321084, baseEnd_1321084] using wordTrace_append hprefix tailTrace_1321084
  have hstable : (prefixWord ++ tailWord_1321084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321084).length < 2 ^ (prefixWord ++ tailWord_1321084).sum := by decide
  have hdescent : baseEnd_1321084 < baseStart_1321084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321098 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1321098 : Nat := 118140960795 + 1321098 * 2 ^ 59
def prefixEnd_1321098 : Nat := 4983230072969 + 3 ^ 40 * 1321098 * 2
def baseEnd_1321098 : Nat := 678358265693577431699387

theorem tailTrace_1321098 : CollatzResearch.WordTrace tailWord_1321098 prefixEnd_1321098 678358265693577431699387 := by
  unfold tailWord_1321098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046100641973761605134987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32122935045263364280359965 12046100641973761605134987)
  ·
    refine ⟨18069150962960642407702481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12046100641973761605134987 18069150962960642407702481)
    ·
      refine ⟨13551863222220481805776861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18069150962960642407702481 13551863222220481805776861)
      ·
        refine ⟨5081948708332680677166323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13551863222220481805776861 5081948708332680677166323)
        ·
          refine ⟨7622923062499021015749485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081948708332680677166323 7622923062499021015749485)
          ·
            refine ⟨2858596148437132880906057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7622923062499021015749485 2858596148437132880906057)
            ·
              refine ⟨2143947111327849660679543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858596148437132880906057 2143947111327849660679543)
              ·
                refine ⟨3215920666991774491019315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143947111327849660679543 3215920666991774491019315)
                ·
                  refine ⟨4823881000487661736528973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215920666991774491019315 4823881000487661736528973)
                  ·
                    refine ⟨1808955375182873151198365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4823881000487661736528973 1808955375182873151198365)
                    ·
                      refine ⟨678358265693577431699387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1808955375182873151198365 678358265693577431699387)
                      ·
                        rfl

theorem cell23_1321098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1321098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321098 prefixEnd_1321098 := by exact prefixLift 1321098
  have htrace : WordTrace (prefixWord ++ tailWord_1321098) baseStart_1321098 baseEnd_1321098 := by
    simpa [prefixWord, tailWord_1321098, baseEnd_1321098] using wordTrace_append hprefix tailTrace_1321098
  have hstable : (prefixWord ++ tailWord_1321098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321098).length < 2 ^ (prefixWord ++ tailWord_1321098).sum := by decide
  have hdescent : baseEnd_1321098 < baseStart_1321098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321104 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_1321104 : Nat := 118140960795 + 1321104 * 2 ^ 59
def prefixEnd_1321104 : Nat := 4983230072969 + 3 ^ 40 * 1321104 * 2
def baseEnd_1321104 : Nat := 678361346577504408224359

theorem tailTrace_1321104 : CollatzResearch.WordTrace tailWord_1321104 prefixEnd_1321104 678361346577504408224359 := by
  unfold tailWord_1321104
  simp only [CollatzResearch.WordTrace]
  refine ⟨24092310702936654722629183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32123080937248872963505577 24092310702936654722629183)
  ·
    refine ⟨36138466054404982083943775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24092310702936654722629183 36138466054404982083943775)
    ·
      refine ⟨54207699081607473125915663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36138466054404982083943775 54207699081607473125915663)
      ·
        refine ⟨81311548622411209688873495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54207699081607473125915663 81311548622411209688873495)
        ·
          refine ⟨121967322933616814533310243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81311548622411209688873495 121967322933616814533310243)
          ·
            refine ⟨182950984400425221799965365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121967322933616814533310243 182950984400425221799965365)
            ·
              refine ⟨17151654787539864543746753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182950984400425221799965365 17151654787539864543746753)
              ·
                refine ⟨12863741090654898407810065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17151654787539864543746753 12863741090654898407810065)
                ·
                  refine ⟨9647805817991173805857549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12863741090654898407810065 9647805817991173805857549)
                  ·
                    refine ⟨3617927181746690177196581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9647805817991173805857549 3617927181746690177196581)
                    ·
                      refine ⟨678361346577504408224359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3617927181746690177196581 678361346577504408224359)
                      ·
                        rfl

theorem cell23_1321104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_1321104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321104 prefixEnd_1321104 := by exact prefixLift 1321104
  have htrace : WordTrace (prefixWord ++ tailWord_1321104) baseStart_1321104 baseEnd_1321104 := by
    simpa [prefixWord, tailWord_1321104, baseEnd_1321104] using wordTrace_append hprefix tailTrace_1321104
  have hstable : (prefixWord ++ tailWord_1321104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321104).length < 2 ^ (prefixWord ++ tailWord_1321104).sum := by decide
  have hdescent : baseEnd_1321104 < baseStart_1321104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321178 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_1321178 : Nat := 118140960795 + 1321178 * 2 ^ 59
def prefixEnd_1321178 : Nat := 4983230072969 + 3 ^ 40 * 1321178 * 2
def baseEnd_1321178 : Nat := 75377704905104124299891

theorem tailTrace_1321178 : CollatzResearch.WordTrace tailWord_1321178 prefixEnd_1321178 75377704905104124299891 := by
  unfold tailWord_1321178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046830101901305020863047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32124880271736813388968125 12046830101901305020863047)
  ·
    refine ⟨18070245152851957531294571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12046830101901305020863047 18070245152851957531294571)
    ·
      refine ⟨27105367729277936296941857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18070245152851957531294571 27105367729277936296941857)
      ·
        refine ⟨20329025796958452222706393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27105367729277936296941857 20329025796958452222706393)
        ·
          refine ⟨15246769347718839167029795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20329025796958452222706393 15246769347718839167029795)
          ·
            refine ⟨22870154021578258750544693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15246769347718839167029795 22870154021578258750544693)
            ·
              refine ⟨2144076939522961757863565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22870154021578258750544693 2144076939522961757863565)
              ·
                refine ⟨804028852321110659198837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2144076939522961757863565 804028852321110659198837)
                ·
                  refine ⟨75377704905104124299891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 804028852321110659198837 75377704905104124299891)
                  ·
                    rfl

theorem cell23_1321178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_1321178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321178 prefixEnd_1321178 := by exact prefixLift 1321178
  have htrace : WordTrace (prefixWord ++ tailWord_1321178) baseStart_1321178 baseEnd_1321178 := by
    simpa [prefixWord, tailWord_1321178, baseEnd_1321178] using wordTrace_append hprefix tailTrace_1321178
  have hstable : (prefixWord ++ tailWord_1321178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321178).length < 2 ^ (prefixWord ++ tailWord_1321178).sum := by decide
  have hdescent : baseEnd_1321178 < baseStart_1321178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321198 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_1321198 : Nat := 118140960795 + 1321198 * 2 ^ 59
def prefixEnd_1321198 : Nat := 4983230072969 + 3 ^ 40 * 1321198 * 2
def baseEnd_1321198 : Nat := 678409613759027040448927

theorem tailTrace_1321198 : CollatzResearch.WordTrace tailWord_1321198 prefixEnd_1321198 678409613759027040448927 := by
  unfold tailWord_1321198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023506233441595437397531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32125366578355175666120165 6023506233441595437397531)
  ·
    refine ⟨9035259350162393156096297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6023506233441595437397531 9035259350162393156096297)
    ·
      refine ⟨6776444512621794867072223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9035259350162393156096297 6776444512621794867072223)
      ·
        refine ⟨10164666768932692300608335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6776444512621794867072223 10164666768932692300608335)
        ·
          refine ⟨15247000153399038450912503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10164666768932692300608335 15247000153399038450912503)
          ·
            refine ⟨22870500230098557676368755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15247000153399038450912503 22870500230098557676368755)
            ·
              refine ⟨34305750345147836514553133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22870500230098557676368755 34305750345147836514553133)
              ·
                refine ⟨12864656379430438692957425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34305750345147836514553133 12864656379430438692957425)
                ·
                  refine ⟨9648492284572829019718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12864656379430438692957425 9648492284572829019718069)
                  ·
                    refine ⟨904546151678702720598569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9648492284572829019718069 904546151678702720598569)
                    ·
                      refine ⟨678409613759027040448927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904546151678702720598569 678409613759027040448927)
                      ·
                        rfl

theorem cell23_1321198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_1321198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321198 prefixEnd_1321198 := by exact prefixLift 1321198
  have htrace : WordTrace (prefixWord ++ tailWord_1321198) baseStart_1321198 baseEnd_1321198 := by
    simpa [prefixWord, tailWord_1321198, baseEnd_1321198] using wordTrace_append hprefix tailTrace_1321198
  have hstable : (prefixWord ++ tailWord_1321198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321198).length < 2 ^ (prefixWord ++ tailWord_1321198).sum := by decide
  have hdescent : baseEnd_1321198 < baseStart_1321198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321228 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1321228 : Nat := 118140960795 + 1321228 * 2 ^ 59
def prefixEnd_1321228 : Nat := 4983230072969 + 3 ^ 40 * 1321228 * 2
def baseEnd_1321228 : Nat := 678425018178661923073789

theorem tailTrace_1321228 : CollatzResearch.WordTrace tailWord_1321228 prefixEnd_1321228 678425018178661923073789 := by
  unfold tailWord_1321228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24094572028712039311386169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32126096038282719081848225 24094572028712039311386169)
  ·
    refine ⟨18070929021534029483539627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24094572028712039311386169 18070929021534029483539627)
    ·
      refine ⟨27106393532301044225309441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18070929021534029483539627 27106393532301044225309441)
      ·
        refine ⟨20329795149225783168982081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27106393532301044225309441 20329795149225783168982081)
        ·
          refine ⟨15247346361919337376736561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20329795149225783168982081 15247346361919337376736561)
          ·
            refine ⟨11435509771439503032552421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15247346361919337376736561 11435509771439503032552421)
            ·
              refine ⟨2144158082144906818603579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11435509771439503032552421 2144158082144906818603579)
              ·
                refine ⟨3216237123217360227905369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144158082144906818603579 3216237123217360227905369)
                ·
                  refine ⟨2412177842413020170929027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3216237123217360227905369 2412177842413020170929027)
                  ·
                    refine ⟨3618266763619530256393541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2412177842413020170929027 3618266763619530256393541)
                    ·
                      refine ⟨678425018178661923073789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3618266763619530256393541 678425018178661923073789)
                      ·
                        rfl

theorem cell23_1321228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1321228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321228 prefixEnd_1321228 := by exact prefixLift 1321228
  have htrace : WordTrace (prefixWord ++ tailWord_1321228) baseStart_1321228 baseEnd_1321228 := by
    simpa [prefixWord, tailWord_1321228, baseEnd_1321228] using wordTrace_append hprefix tailTrace_1321228
  have hstable : (prefixWord ++ tailWord_1321228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321228).length < 2 ^ (prefixWord ++ tailWord_1321228).sum := by decide
  have hdescent : baseEnd_1321228 < baseStart_1321228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321231 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_1321231 : Nat := 118140960795 + 1321231 * 2 ^ 59
def prefixEnd_1321231 : Nat := 4983230072969 + 3 ^ 40 * 1321231 * 2
def baseEnd_1321231 : Nat := 678426558620625411336275

theorem tailTrace_1321231 : CollatzResearch.WordTrace tailWord_1321231 prefixEnd_1321231 678426558620625411336275 := by
  unfold tailWord_1321231
  simp only [CollatzResearch.WordTrace]
  refine ⟨48189253476413210135131547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32126168984275473423421031 48189253476413210135131547)
  ·
    refine ⟨72283880214619815202697321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48189253476413210135131547 72283880214619815202697321)
    ·
      refine ⟨54212910160964861402022991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72283880214619815202697321 54212910160964861402022991)
      ·
        refine ⟨81319365241447292103034487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54212910160964861402022991 81319365241447292103034487)
        ·
          refine ⟨121979047862170938154551731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81319365241447292103034487 121979047862170938154551731)
          ·
            refine ⟨182968571793256407231827597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121979047862170938154551731 182968571793256407231827597)
            ·
              refine ⟨68613214422471152711935349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182968571793256407231827597 68613214422471152711935349)
              ·
                refine ⟨6432488852106670566743939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68613214422471152711935349 6432488852106670566743939)
                ·
                  refine ⟨9648733278160005850115909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432488852106670566743939 9648733278160005850115909)
                  ·
                    refine ⟨1809137489655001096896733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9648733278160005850115909 1809137489655001096896733)
                    ·
                      refine ⟨678426558620625411336275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1809137489655001096896733 678426558620625411336275)
                      ·
                        rfl

theorem cell23_1321231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_1321231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321231 prefixEnd_1321231 := by exact prefixLift 1321231
  have htrace : WordTrace (prefixWord ++ tailWord_1321231) baseStart_1321231 baseEnd_1321231 := by
    simpa [prefixWord, tailWord_1321231, baseEnd_1321231] using wordTrace_append hprefix tailTrace_1321231
  have hstable : (prefixWord ++ tailWord_1321231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321231).length < 2 ^ (prefixWord ++ tailWord_1321231).sum := by decide
  have hdescent : baseEnd_1321231 < baseStart_1321231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321311 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 3, 6]
def baseStart_1321311 : Nat := 118140960795 + 1321311 * 2 ^ 59
def prefixEnd_1321311 : Nat := 4983230072969 + 3 ^ 40 * 1321311 * 2
def baseEnd_1321311 : Nat := 226155879024328366111969

theorem tailTrace_1321311 : CollatzResearch.WordTrace tailWord_1321311 prefixEnd_1321311 226155879024328366111969 := by
  unfold tailWord_1321311
  simp only [CollatzResearch.WordTrace]
  refine ⟨48192171316123383798043787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32128114210748922532029191 48192171316123383798043787)
  ·
    refine ⟨72288256974185075697065681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48192171316123383798043787 72288256974185075697065681)
    ·
      refine ⟨54216192730638806772799261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72288256974185075697065681 54216192730638806772799261)
      ·
        refine ⟨20331072273989552539799723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54216192730638806772799261 20331072273989552539799723)
        ·
          refine ⟨30496608410984328809699585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20331072273989552539799723 30496608410984328809699585)
          ·
            refine ⟨22872456308238246607274689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30496608410984328809699585 22872456308238246607274689)
            ·
              refine ⟨17154342231178684955456017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22872456308238246607274689 17154342231178684955456017)
              ·
                refine ⟨12865756673384013716592013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17154342231178684955456017 12865756673384013716592013)
                ·
                  refine ⟨4824658752519005143722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12865756673384013716592013 4824658752519005143722005)
                  ·
                    refine ⟨226155879024328366111969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4824658752519005143722005 226155879024328366111969)
                    ·
                      rfl

theorem cell23_1321311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_1321311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321311 prefixEnd_1321311 := by exact prefixLift 1321311
  have htrace : WordTrace (prefixWord ++ tailWord_1321311) baseStart_1321311 baseEnd_1321311 := by
    simpa [prefixWord, tailWord_1321311, baseEnd_1321311] using wordTrace_append hprefix tailTrace_1321311
  have hstable : (prefixWord ++ tailWord_1321311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321311).length < 2 ^ (prefixWord ++ tailWord_1321311).sum := by decide
  have hdescent : baseEnd_1321311 < baseStart_1321311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321312 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 3, 1, 3]
def baseStart_1321312 : Nat := 118140960795 + 1321312 * 2 ^ 59
def prefixEnd_1321312 : Nat := 4983230072969 + 3 ^ 40 * 1321312 * 2
def baseEnd_1321312 : Nat := 678468150553639594423403

theorem tailTrace_1321312 : CollatzResearch.WordTrace tailWord_1321312 prefixEnd_1321312 678468150553639594423403 := by
  unfold tailWord_1321312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24096103894559880484415095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32128138526079840645886793 24096103894559880484415095)
  ·
    refine ⟨36144155841839820726622643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24096103894559880484415095 36144155841839820726622643)
    ·
      refine ⟨54216233762759731089933965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36144155841839820726622643 54216233762759731089933965)
      ·
        refine ⟨20331087661034899158725237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54216233762759731089933965 20331087661034899158725237)
        ·
          refine ⟨1906039468222021796130491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20331087661034899158725237 1906039468222021796130491)
          ·
            refine ⟨2859059202333032694195737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906039468222021796130491 2859059202333032694195737)
            ·
              refine ⟨2144294401749774520646803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859059202333032694195737 2144294401749774520646803)
              ·
                refine ⟨3216441602624661780970205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144294401749774520646803 3216441602624661780970205)
                ·
                  refine ⟨1206165600984248167863827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3216441602624661780970205 1206165600984248167863827)
                  ·
                    refine ⟨1809248401476372251795741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1206165600984248167863827 1809248401476372251795741)
                    ·
                      refine ⟨678468150553639594423403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1809248401476372251795741 678468150553639594423403)
                      ·
                        rfl

theorem cell23_1321312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_1321312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321312 prefixEnd_1321312 := by exact prefixLift 1321312
  have htrace : WordTrace (prefixWord ++ tailWord_1321312) baseStart_1321312 baseEnd_1321312 := by
    simpa [prefixWord, tailWord_1321312, baseEnd_1321312] using wordTrace_append hprefix tailTrace_1321312
  have hstable : (prefixWord ++ tailWord_1321312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321312).length < 2 ^ (prefixWord ++ tailWord_1321312).sum := by decide
  have hdescent : baseEnd_1321312 < baseStart_1321312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321328 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 1, 6]
def baseStart_1321328 : Nat := 118140960795 + 1321328 * 2 ^ 59
def prefixEnd_1321328 : Nat := 4983230072969 + 3 ^ 40 * 1321328 * 2
def baseEnd_1321328 : Nat := 226158788748037177274443

theorem tailTrace_1321328 : CollatzResearch.WordTrace tailWord_1321328 prefixEnd_1321328 226158788748037177274443 := by
  unfold tailWord_1321328
  simp only [CollatzResearch.WordTrace]
  refine ⟨24096395678530897850706319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32128527571374530467608425 24096395678530897850706319)
  ·
    refine ⟨36144593517796346776059479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24096395678530897850706319 36144593517796346776059479)
    ·
      refine ⟨54216890276694520164089219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36144593517796346776059479 54216890276694520164089219)
      ·
        refine ⟨81325335415041780246133829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54216890276694520164089219 81325335415041780246133829)
        ·
          refine ⟨15248500390320333796150093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81325335415041780246133829 15248500390320333796150093)
          ·
            refine ⟨5718187646370125173556285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15248500390320333796150093 5718187646370125173556285)
            ·
              refine ⟨2144320367388796940083607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5718187646370125173556285 2144320367388796940083607)
              ·
                refine ⟨3216480551083195410125411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144320367388796940083607 3216480551083195410125411)
                ·
                  refine ⟨4824720826624793115188117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216480551083195410125411 4824720826624793115188117)
                  ·
                    refine ⟨226158788748037177274443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4824720826624793115188117 226158788748037177274443)
                    ·
                      rfl

theorem cell23_1321328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_1321328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321328 prefixEnd_1321328 := by exact prefixLift 1321328
  have htrace : WordTrace (prefixWord ++ tailWord_1321328) baseStart_1321328 baseEnd_1321328 := by
    simpa [prefixWord, tailWord_1321328, baseEnd_1321328] using wordTrace_append hprefix tailTrace_1321328
  have hstable : (prefixWord ++ tailWord_1321328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321328).length < 2 ^ (prefixWord ++ tailWord_1321328).sum := by decide
  have hdescent : baseEnd_1321328 < baseStart_1321328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321331 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6]
def baseStart_1321331 : Nat := 118140960795 + 1321331 * 2 ^ 59
def prefixEnd_1321331 : Nat := 4983230072969 + 3 ^ 40 * 1321331 * 2
def baseEnd_1321331 : Nat := 678477906686075020085815

theorem tailTrace_1321331 : CollatzResearch.WordTrace tailWord_1321331 prefixEnd_1321331 678477906686075020085815 := by
  unfold tailWord_1321331
  simp only [CollatzResearch.WordTrace]
  refine ⟨48192900776050927213771847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32128600517367284809181231 48192900776050927213771847)
  ·
    refine ⟨72289351164076390820657771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48192900776050927213771847 72289351164076390820657771)
    ·
      refine ⟨108434026746114586230986657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72289351164076390820657771 108434026746114586230986657)
      ·
        refine ⟨81325520059585939673239993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108434026746114586230986657 81325520059585939673239993)
        ·
          refine ⟨60994140044689454754929995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81325520059585939673239993 60994140044689454754929995)
          ·
            refine ⟨91491210067034182132394993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60994140044689454754929995 91491210067034182132394993)
            ·
              refine ⟨68618407550275636599296245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91491210067034182132394993 68618407550275636599296245)
              ·
                refine ⟨6432975707838340931184023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68618407550275636599296245 6432975707838340931184023)
                ·
                  refine ⟨9649463561757511396776035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432975707838340931184023 9649463561757511396776035)
                  ·
                    refine ⟨14474195342636267095164053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9649463561757511396776035 14474195342636267095164053)
                    ·
                      refine ⟨678477906686075020085815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14474195342636267095164053 678477906686075020085815)
                      ·
                        rfl

theorem cell23_1321331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_1321331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321331 prefixEnd_1321331 := by exact prefixLift 1321331
  have htrace : WordTrace (prefixWord ++ tailWord_1321331) baseStart_1321331 baseEnd_1321331 := by
    simpa [prefixWord, tailWord_1321331, baseEnd_1321331] using wordTrace_append hprefix tailTrace_1321331
  have hstable : (prefixWord ++ tailWord_1321331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321331).length < 2 ^ (prefixWord ++ tailWord_1321331).sum := by decide
  have hdescent : baseEnd_1321331 < baseStart_1321331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321335 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 5, 2, 2]
def baseStart_1321335 : Nat := 118140960795 + 1321335 * 2 ^ 59
def prefixEnd_1321335 : Nat := 4983230072969 + 3 ^ 40 * 1321335 * 2
def baseEnd_1321335 : Nat := 678479960608693004435797

theorem tailTrace_1321335 : CollatzResearch.WordTrace tailWord_1321335 prefixEnd_1321335 678479960608693004435797 := by
  unfold tailWord_1321335
  simp only [CollatzResearch.WordTrace]
  refine ⟨48193046668036435896917459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32128697778690957264611639 48193046668036435896917459)
  ·
    refine ⟨72289570002054653845376189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48193046668036435896917459 72289570002054653845376189)
    ·
      refine ⟨27108588750770495192016071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72289570002054653845376189 27108588750770495192016071)
      ·
        refine ⟨40662883126155742788024107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27108588750770495192016071 40662883126155742788024107)
        ·
          refine ⟨60994324689233614182036161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40662883126155742788024107 60994324689233614182036161)
          ·
            refine ⟨45745743516925210636527121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60994324689233614182036161 45745743516925210636527121)
            ·
              refine ⟨34309307637693907977395341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45745743516925210636527121 34309307637693907977395341)
              ·
                refine ⟨12865990364135215491523253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34309307637693907977395341 12865990364135215491523253)
                ·
                  refine ⟨1206186596637676452330305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12865990364135215491523253 1206186596637676452330305)
                  ·
                    refine ⟨904639947478257339247729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1206186596637676452330305 904639947478257339247729)
                    ·
                      refine ⟨678479960608693004435797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904639947478257339247729 678479960608693004435797)
                      ·
                        rfl

theorem cell23_1321335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_1321335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321335 prefixEnd_1321335 := by exact prefixLift 1321335
  have htrace : WordTrace (prefixWord ++ tailWord_1321335) baseStart_1321335 baseEnd_1321335 := by
    simpa [prefixWord, tailWord_1321335, baseEnd_1321335] using wordTrace_append hprefix tailTrace_1321335
  have hstable : (prefixWord ++ tailWord_1321335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321335).length < 2 ^ (prefixWord ++ tailWord_1321335).sum := by decide
  have hdescent : baseEnd_1321335 < baseStart_1321335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321345 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1321345 : Nat := 118140960795 + 1321345 * 2 ^ 59
def prefixEnd_1321345 : Nat := 4983230072969 + 3 ^ 40 * 1321345 * 2
def baseEnd_1321345 : Nat := 226161698471745988436917

theorem tailTrace_1321345 : CollatzResearch.WordTrace tailWord_1321345 prefixEnd_1321345 226161698471745988436917 := by
  unfold tailWord_1321345
  simp only [CollatzResearch.WordTrace]
  refine ⟨48193411398000207604781489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32128940932000138403187659 48193411398000207604781489)
  ·
    refine ⟨36145058548500155703586117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48193411398000207604781489 36145058548500155703586117)
    ·
      refine ⟨6777198477843779194422397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36145058548500155703586117 6777198477843779194422397)
      ·
        refine ⟨2541449429191417197908399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6777198477843779194422397 2541449429191417197908399)
        ·
          refine ⟨3812174143787125796862599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541449429191417197908399 3812174143787125796862599)
          ·
            refine ⟨5718261215680688695293899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812174143787125796862599 5718261215680688695293899)
            ·
              refine ⟨8577391823521033042940849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718261215680688695293899 8577391823521033042940849)
              ·
                refine ⟨6433043867640774782205637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8577391823521033042940849 6433043867640774782205637)
                ·
                  refine ⟨1206195725182645271663557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6433043867640774782205637 1206195725182645271663557)
                  ·
                    refine ⟨226161698471745988436917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1206195725182645271663557 226161698471745988436917)
                    ·
                      rfl

theorem cell23_1321345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1321345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321345 prefixEnd_1321345 := by exact prefixLift 1321345
  have htrace : WordTrace (prefixWord ++ tailWord_1321345) baseStart_1321345 baseEnd_1321345 := by
    simpa [prefixWord, tailWord_1321345, baseEnd_1321345] using wordTrace_append hprefix tailTrace_1321345
  have hstable : (prefixWord ++ tailWord_1321345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321345).length < 2 ^ (prefixWord ++ tailWord_1321345).sum := by decide
  have hdescent : baseEnd_1321345 < baseStart_1321345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321348 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1321348 : Nat := 118140960795 + 1321348 * 2 ^ 59
def prefixEnd_1321348 : Nat := 4983230072969 + 3 ^ 40 * 1321348 * 2
def baseEnd_1321348 : Nat := 678486635857201453573237

theorem tailTrace_1321348 : CollatzResearch.WordTrace tailWord_1321348 prefixEnd_1321348 678486635857201453573237 := by
  unfold tailWord_1321348
  simp only [CollatzResearch.WordTrace]
  refine ⟨24096760408494669558570349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32129013877992892744760465 24096760408494669558570349)
  ·
    refine ⟨9036285153185501084463881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24096760408494669558570349 9036285153185501084463881)
    ·
      refine ⟨6777213864889125813347911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9036285153185501084463881 6777213864889125813347911)
      ·
        refine ⟨10165820797333688720021867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6777213864889125813347911 10165820797333688720021867)
        ·
          refine ⟨15248731196000533080032801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10165820797333688720021867 15248731196000533080032801)
          ·
            refine ⟨11436548397000399810024601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15248731196000533080032801 11436548397000399810024601)
            ·
              refine ⟨8577411297750299857518451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11436548397000399810024601 8577411297750299857518451)
              ·
                refine ⟨12866116946625449786277677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577411297750299857518451 12866116946625449786277677)
                ·
                  refine ⟨4824793854984543669854129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12866116946625449786277677 4824793854984543669854129)
                  ·
                    refine ⟨3618595391238407752390597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4824793854984543669854129 3618595391238407752390597)
                    ·
                      refine ⟨678486635857201453573237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3618595391238407752390597 678486635857201453573237)
                      ·
                        rfl

theorem cell23_1321348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1321348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321348 prefixEnd_1321348 := by exact prefixLift 1321348
  have htrace : WordTrace (prefixWord ++ tailWord_1321348) baseStart_1321348 baseEnd_1321348 := by
    simpa [prefixWord, tailWord_1321348, baseEnd_1321348] using wordTrace_append hprefix tailTrace_1321348
  have hstable : (prefixWord ++ tailWord_1321348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321348).length < 2 ^ (prefixWord ++ tailWord_1321348).sum := by decide
  have hdescent : baseEnd_1321348 < baseStart_1321348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321355 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 3]
def baseStart_1321355 : Nat := 118140960795 + 1321355 * 2 ^ 59
def prefixEnd_1321355 : Nat := 4983230072969 + 3 ^ 40 * 1321355 * 2
def baseEnd_1321355 : Nat := 678490230221782926185705

theorem tailTrace_1321355 : CollatzResearch.WordTrace tailWord_1321355 prefixEnd_1321355 678490230221782926185705 := by
  unfold tailWord_1321355
  simp only [CollatzResearch.WordTrace]
  refine ⟨48193776127963979312645519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32129184085309319541763679 48193776127963979312645519)
  ·
    refine ⟨72290664191945968968968279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48193776127963979312645519 72290664191945968968968279)
    ·
      refine ⟨108435996287918953453452419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72290664191945968968968279 108435996287918953453452419)
      ·
        refine ⟨162653994431878430180178629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108435996287918953453452419 162653994431878430180178629)
        ·
          refine ⟨30497623955977205658783493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162653994431878430180178629 30497623955977205658783493)
          ·
            refine ⟨5718304491745726061021905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30497623955977205658783493 5718304491745726061021905)
            ·
              refine ⟨4288728368809294545766429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5718304491745726061021905 4288728368809294545766429)
              ·
                refine ⟨1608273138303485454662411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4288728368809294545766429 1608273138303485454662411)
                ·
                  refine ⟨2412409707455228181993617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608273138303485454662411 2412409707455228181993617)
                  ·
                    refine ⟨1809307280591421136495213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2412409707455228181993617 1809307280591421136495213)
                    ·
                      refine ⟨678490230221782926185705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1809307280591421136495213 678490230221782926185705)
                      ·
                        rfl

theorem cell23_1321355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 3].length) (baseStart_1321355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321355 prefixEnd_1321355 := by exact prefixLift 1321355
  have htrace : WordTrace (prefixWord ++ tailWord_1321355) baseStart_1321355 baseEnd_1321355 := by
    simpa [prefixWord, tailWord_1321355, baseEnd_1321355] using wordTrace_append hprefix tailTrace_1321355
  have hstable : (prefixWord ++ tailWord_1321355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321355).length < 2 ^ (prefixWord ++ tailWord_1321355).sum := by decide
  have hdescent : baseEnd_1321355 < baseStart_1321355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321358 : List Nat := [4, 1, 1, 4, 1, 1, 11]
def baseStart_1321358 : Nat := 118140960795 + 1321358 * 2 ^ 59
def prefixEnd_1321358 : Nat := 4983230072969 + 3 ^ 40 * 1321358 * 2
def baseEnd_1321358 : Nat := 8376441613132671783311

theorem tailTrace_1321358 : CollatzResearch.WordTrace tailWord_1321358 prefixEnd_1321358 8376441613132671783311 := by
  unfold tailWord_1321358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024235693369138853125591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32129257031302073883336485 6024235693369138853125591)
  ·
    refine ⟨9036353540053708279688387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6024235693369138853125591 9036353540053708279688387)
    ·
      refine ⟨13554530310080562419532581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9036353540053708279688387 13554530310080562419532581)
      ·
        refine ⟨2541474433140105453662359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13554530310080562419532581 2541474433140105453662359)
        ·
          refine ⟨3812211649710158180493539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541474433140105453662359 3812211649710158180493539)
          ·
            refine ⟨5718317474565237270740309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812211649710158180493539 5718317474565237270740309)
            ·
              refine ⟨8376441613132671783311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5718317474565237270740309 8376441613132671783311)
              ·
                rfl

theorem cell23_1321358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 11].length) (baseStart_1321358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321358 prefixEnd_1321358 := by exact prefixLift 1321358
  have htrace : WordTrace (prefixWord ++ tailWord_1321358) baseStart_1321358 baseEnd_1321358 := by
    simpa [prefixWord, tailWord_1321358, baseEnd_1321358] using wordTrace_append hprefix tailTrace_1321358
  have hstable : (prefixWord ++ tailWord_1321358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321358).length < 2 ^ (prefixWord ++ tailWord_1321358).sum := by decide
  have hdescent : baseEnd_1321358 < baseStart_1321358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321361 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_1321361 : Nat := 118140960795 + 1321361 * 2 ^ 59
def prefixEnd_1321361 : Nat := 4983230072969 + 3 ^ 40 * 1321361 * 2
def baseEnd_1321361 : Nat := 678493311105709902710677

theorem tailTrace_1321361 : CollatzResearch.WordTrace tailWord_1321361 prefixEnd_1321361 678493311105709902710677 := by
  unfold tailWord_1321361
  simp only [CollatzResearch.WordTrace]
  refine ⟨48193994965942242337363937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32129329977294828224909291 48193994965942242337363937)
  ·
    refine ⟨36145496224456681753022953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48193994965942242337363937 36145496224456681753022953)
    ·
      refine ⟨27109122168342511314767215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36145496224456681753022953 27109122168342511314767215)
      ·
        refine ⟨40663683252513766972150823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27109122168342511314767215 40663683252513766972150823)
        ·
          refine ⟨60995524878770650458226235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40663683252513766972150823 60995524878770650458226235)
          ·
            refine ⟨91493287318155975687339353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60995524878770650458226235 91493287318155975687339353)
            ·
              refine ⟨68619965488616981765504515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91493287318155975687339353 68619965488616981765504515)
              ·
                refine ⟨102929948232925472648256773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68619965488616981765504515 102929948232925472648256773)
                ·
                  refine ⟨19299365293673526121548145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102929948232925472648256773 19299365293673526121548145)
                  ·
                    refine ⟨14474523970255144591161109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19299365293673526121548145 14474523970255144591161109)
                    ·
                      refine ⟨678493311105709902710677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14474523970255144591161109 678493311105709902710677)
                      ·
                        rfl

theorem cell23_1321361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_1321361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321361 prefixEnd_1321361 := by exact prefixLift 1321361
  have htrace : WordTrace (prefixWord ++ tailWord_1321361) baseStart_1321361 baseEnd_1321361 := by
    simpa [prefixWord, tailWord_1321361, baseEnd_1321361] using wordTrace_append hprefix tailTrace_1321361
  have hstable : (prefixWord ++ tailWord_1321361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321361).length < 2 ^ (prefixWord ++ tailWord_1321361).sum := by decide
  have hdescent : baseEnd_1321361 < baseStart_1321361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321378 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1321378 : Nat := 118140960795 + 1321378 * 2 ^ 59
def prefixEnd_1321378 : Nat := 4983230072969 + 3 ^ 40 * 1321378 * 2
def baseEnd_1321378 : Nat := 678502040276836336198099

theorem tailTrace_1321378 : CollatzResearch.WordTrace tailWord_1321378 prefixEnd_1321378 678502040276836336198099 := by
  unfold tailWord_1321378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12048653751720163560183197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32129743337920436160488525 12048653751720163560183197)
  ·
    refine ⟨4518245156895061335068699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12048653751720163560183197 4518245156895061335068699)
    ·
      refine ⟨6777367735342592002603049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518245156895061335068699 6777367735342592002603049)
      ·
        refine ⟨5083025801506944001952287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6777367735342592002603049 5083025801506944001952287)
        ·
          refine ⟨7624538702260416002928431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083025801506944001952287 7624538702260416002928431)
          ·
            refine ⟨11436808053390624004392647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624538702260416002928431 11436808053390624004392647)
            ·
              refine ⟨17155212080085936006588971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11436808053390624004392647 17155212080085936006588971)
              ·
                refine ⟨25732818120128904009883457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17155212080085936006588971 25732818120128904009883457)
                ·
                  refine ⟨19299613590096678007412593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25732818120128904009883457 19299613590096678007412593)
                  ·
                    refine ⟨14474710192572508505559445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19299613590096678007412593 14474710192572508505559445)
                    ·
                      refine ⟨678502040276836336198099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14474710192572508505559445 678502040276836336198099)
                      ·
                        rfl

theorem cell23_1321378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1321378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321378 prefixEnd_1321378 := by exact prefixLift 1321378
  have htrace : WordTrace (prefixWord ++ tailWord_1321378) baseStart_1321378 baseEnd_1321378 := by
    simpa [prefixWord, tailWord_1321378, baseEnd_1321378] using wordTrace_append hprefix tailTrace_1321378
  have hstable : (prefixWord ++ tailWord_1321378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321378).length < 2 ^ (prefixWord ++ tailWord_1321378).sum := by decide
  have hdescent : baseEnd_1321378 < baseStart_1321378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321391 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_1321391 : Nat := 118140960795 + 1321391 * 2 ^ 59
def prefixEnd_1321391 : Nat := 4983230072969 + 3 ^ 40 * 1321391 * 2
def baseEnd_1321391 : Nat := 678508715525344785335539

theorem tailTrace_1321391 : CollatzResearch.WordTrace tailWord_1321391 prefixEnd_1321391 678508715525344785335539 := by
  unfold tailWord_1321391
  simp only [CollatzResearch.WordTrace]
  refine ⟨48195089155833557460956027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32130059437222371640637351 48195089155833557460956027)
  ·
    refine ⟨72292633733750336191434041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48195089155833557460956027 72292633733750336191434041)
    ·
      refine ⟨54219475300312752143575531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72292633733750336191434041 54219475300312752143575531)
      ·
        refine ⟨81329212950469128215363297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54219475300312752143575531 81329212950469128215363297)
        ·
          refine ⟨60996909712851846161522473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81329212950469128215363297 60996909712851846161522473)
          ·
            refine ⟨45747682284638884621141855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60996909712851846161522473 45747682284638884621141855)
            ·
              refine ⟨68621523426958326931712783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45747682284638884621141855 68621523426958326931712783)
              ·
                refine ⟨102932285140437490397569175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68621523426958326931712783 102932285140437490397569175)
                ·
                  refine ⟨154398427710656235596353763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102932285140437490397569175 154398427710656235596353763)
                  ·
                    refine ⟨231597641565984353394530645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154398427710656235596353763 231597641565984353394530645)
                    ·
                      refine ⟨678508715525344785335539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 231597641565984353394530645 678508715525344785335539)
                      ·
                        rfl

theorem cell23_1321391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_1321391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321391 prefixEnd_1321391 := by exact prefixLift 1321391
  have htrace : WordTrace (prefixWord ++ tailWord_1321391) baseStart_1321391 baseEnd_1321391 := by
    simpa [prefixWord, tailWord_1321391, baseEnd_1321391] using wordTrace_append hprefix tailTrace_1321391
  have hstable : (prefixWord ++ tailWord_1321391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321391).length < 2 ^ (prefixWord ++ tailWord_1321391).sum := by decide
  have hdescent : baseEnd_1321391 < baseStart_1321391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321418 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1321418 : Nat := 118140960795 + 1321418 * 2 ^ 59
def prefixEnd_1321418 : Nat := 4983230072969 + 3 ^ 40 * 1321418 * 2
def baseEnd_1321418 : Nat := 226174193167672059899305

theorem tailTrace_1321418 : CollatzResearch.WordTrace tailWord_1321418 prefixEnd_1321418 226174193167672059899305 := by
  unfold tailWord_1321418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12049018481683935268047227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32130715951157160714792605 12049018481683935268047227)
  ·
    refine ⟨18073527722525902902070841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12049018481683935268047227 18073527722525902902070841)
    ·
      refine ⟨13555145791894427176553131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18073527722525902902070841 13555145791894427176553131)
      ·
        refine ⟨20332718687841640764829697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13555145791894427176553131 20332718687841640764829697)
        ·
          refine ⟨15249539015881230573622273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20332718687841640764829697 15249539015881230573622273)
          ·
            refine ⟨11437154261910922930216705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15249539015881230573622273 11437154261910922930216705)
            ·
              refine ⟨8577865696433192197662529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11437154261910922930216705 8577865696433192197662529)
              ·
                refine ⟨6433399272324894148246897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8577865696433192197662529 6433399272324894148246897)
                ·
                  refine ⟨4825049454243670611185173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6433399272324894148246897 4825049454243670611185173)
                  ·
                    refine ⟨226174193167672059899305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4825049454243670611185173 226174193167672059899305)
                    ·
                      rfl

theorem cell23_1321418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1321418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321418 prefixEnd_1321418 := by exact prefixLift 1321418
  have htrace : WordTrace (prefixWord ++ tailWord_1321418) baseStart_1321418 baseEnd_1321418 := by
    simpa [prefixWord, tailWord_1321418, baseEnd_1321418] using wordTrace_append hprefix tailTrace_1321418
  have hstable : (prefixWord ++ tailWord_1321418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321418).length < 2 ^ (prefixWord ++ tailWord_1321418).sum := by decide
  have hdescent : baseEnd_1321418 < baseStart_1321418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321420 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1321420 : Nat := 118140960795 + 1321420 * 2 ^ 59
def prefixEnd_1321420 : Nat := 4983230072969 + 3 ^ 40 * 1321420 * 2
def baseEnd_1321420 : Nat := 678523606464325171872907

theorem tailTrace_1321420 : CollatzResearch.WordTrace tailWord_1321420 prefixEnd_1321420 678523606464325171872907 := by
  unfold tailWord_1321420
  simp only [CollatzResearch.WordTrace]
  refine ⟨24098073436364247706880857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32130764581818996942507809 24098073436364247706880857)
  ·
    refine ⟨18073555077273185780160643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24098073436364247706880857 18073555077273185780160643)
    ·
      refine ⟨27110332615909778670240965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18073555077273185780160643 27110332615909778670240965)
      ·
        refine ⟨5083187365483083500670181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27110332615909778670240965 5083187365483083500670181)
        ·
          refine ⟨953097631028078156375659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5083187365483083500670181 953097631028078156375659)
          ·
            refine ⟨1429646446542117234563489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953097631028078156375659 1429646446542117234563489)
            ·
              refine ⟨1072234834906587925922617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429646446542117234563489 1072234834906587925922617)
              ·
                refine ⟨804176126179940944441963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072234834906587925922617 804176126179940944441963)
                ·
                  refine ⟨1206264189269911416662945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804176126179940944441963 1206264189269911416662945)
                  ·
                    refine ⟨904698141952433562497209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1206264189269911416662945 904698141952433562497209)
                    ·
                      refine ⟨678523606464325171872907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904698141952433562497209 678523606464325171872907)
                      ·
                        rfl

theorem cell23_1321420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1321420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321420 prefixEnd_1321420 := by exact prefixLift 1321420
  have htrace : WordTrace (prefixWord ++ tailWord_1321420) baseStart_1321420 baseEnd_1321420 := by
    simpa [prefixWord, tailWord_1321420, baseEnd_1321420] using wordTrace_append hprefix tailTrace_1321420
  have hstable : (prefixWord ++ tailWord_1321420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321420).length < 2 ^ (prefixWord ++ tailWord_1321420).sum := by decide
  have hdescent : baseEnd_1321420 < baseStart_1321420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321448 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 9]
def baseStart_1321448 : Nat := 118140960795 + 1321448 * 2 ^ 59
def prefixEnd_1321448 : Nat := 4983230072969 + 3 ^ 40 * 1321448 * 2
def baseEnd_1321448 : Nat := 75393109324739006924753

theorem tailTrace_1321448 : CollatzResearch.WordTrace tailWord_1321448 prefixEnd_1321448 75393109324739006924753 := by
  unfold tailWord_1321448
  simp only [CollatzResearch.WordTrace]
  refine ⟨24098584058313528097890499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32131445411084704130520665 24098584058313528097890499)
  ·
    refine ⟨36147876087470292146835749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24098584058313528097890499 36147876087470292146835749)
    ·
      refine ⟨6777726766400679777531703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36147876087470292146835749 6777726766400679777531703)
      ·
        refine ⟨10166590149601019666297555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6777726766400679777531703 10166590149601019666297555)
        ·
          refine ⟨15249885224401529499446333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10166590149601019666297555 15249885224401529499446333)
          ·
            refine ⟨5718706959150573562292375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15249885224401529499446333 5718706959150573562292375)
            ·
              refine ⟨8578060438725860343438563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718706959150573562292375 8578060438725860343438563)
              ·
                refine ⟨12867090658088790515157845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8578060438725860343438563 12867090658088790515157845)
                ·
                  refine ⟨75393109324739006924753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12867090658088790515157845 75393109324739006924753)
                  ·
                    rfl

theorem cell23_1321448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_1321448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321448 prefixEnd_1321448 := by exact prefixLift 1321448
  have htrace : WordTrace (prefixWord ++ tailWord_1321448) baseStart_1321448 baseEnd_1321448 := by
    simpa [prefixWord, tailWord_1321448, baseEnd_1321448] using wordTrace_append hprefix tailTrace_1321448
  have hstable : (prefixWord ++ tailWord_1321448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321448).length < 2 ^ (prefixWord ++ tailWord_1321448).sum := by decide
  have hdescent : baseEnd_1321448 < baseStart_1321448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321465 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 5]
def baseStart_1321465 : Nat := 118140960795 + 1321465 * 2 ^ 59
def prefixEnd_1321465 : Nat := 4983230072969 + 3 ^ 40 * 1321465 * 2
def baseEnd_1321465 : Nat := 75394079232641943978911

theorem tailTrace_1321465 : CollatzResearch.WordTrace tailWord_1321465 prefixEnd_1321465 75394079232641943978911 := by
  unfold tailWord_1321465
  simp only [CollatzResearch.WordTrace]
  refine ⟨48197788157565468099149849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32131858771710312066099899 48197788157565468099149849)
  ·
    refine ⟨36148341118174101074362387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48197788157565468099149849 36148341118174101074362387)
    ·
      refine ⟨54222511677261151611543581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36148341118174101074362387 54222511677261151611543581)
      ·
        refine ⟨20333441878972931854328843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54222511677261151611543581 20333441878972931854328843)
        ·
          refine ⟨30500162818459397781493265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20333441878972931854328843 30500162818459397781493265)
          ·
            refine ⟨22875122113844548336119949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30500162818459397781493265 22875122113844548336119949)
            ·
              refine ⟨8578170792691705626044981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22875122113844548336119949 8578170792691705626044981)
              ·
                refine ⟨804203511814847402441717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8578170792691705626044981 804203511814847402441717)
                ·
                  refine ⟨75394079232641943978911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 804203511814847402441717 75394079232641943978911)
                  ·
                    rfl

theorem cell23_1321465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 5].length) (baseStart_1321465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321465 prefixEnd_1321465 := by exact prefixLift 1321465
  have htrace : WordTrace (prefixWord ++ tailWord_1321465) baseStart_1321465 baseEnd_1321465 := by
    simpa [prefixWord, tailWord_1321465, baseEnd_1321465] using wordTrace_append hprefix tailTrace_1321465
  have hstable : (prefixWord ++ tailWord_1321465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321465).length < 2 ^ (prefixWord ++ tailWord_1321465).sum := by decide
  have hdescent : baseEnd_1321465 < baseStart_1321465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321476 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1321476 : Nat := 118140960795 + 1321476 * 2 ^ 59
def prefixEnd_1321476 : Nat := 4983230072969 + 3 ^ 40 * 1321476 * 2
def baseEnd_1321476 : Nat := 678552361380976952772649

theorem tailTrace_1321476 : CollatzResearch.WordTrace tailWord_1321476 prefixEnd_1321476 678552361380976952772649 := by
  unfold tailWord_1321476
  simp only [CollatzResearch.WordTrace]
  refine ⟨24099094680262808488900141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32132126240350411318533521 24099094680262808488900141)
  ·
    refine ⟨9037160505098553183337553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24099094680262808488900141 9037160505098553183337553)
    ·
      refine ⟨6777870378823914887503165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9037160505098553183337553 6777870378823914887503165)
      ·
        refine ⟨2541701392058968082813687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6777870378823914887503165 2541701392058968082813687)
        ·
          refine ⟨3812552088088452124220531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541701392058968082813687 3812552088088452124220531)
          ·
            refine ⟨5718828132132678186330797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812552088088452124220531 5718828132132678186330797)
            ·
              refine ⟨2144560549549754319874049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5718828132132678186330797 2144560549549754319874049)
              ·
                refine ⟨1608420412162315739905537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2144560549549754319874049 1608420412162315739905537)
                ·
                  refine ⟨1206315309121736804929153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1608420412162315739905537 1206315309121736804929153)
                  ·
                    refine ⟨904736481841302603696865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1206315309121736804929153 904736481841302603696865)
                    ·
                      refine ⟨678552361380976952772649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904736481841302603696865 678552361380976952772649)
                      ·
                        rfl

theorem cell23_1321476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1321476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321476 prefixEnd_1321476 := by exact prefixLift 1321476
  have htrace : WordTrace (prefixWord ++ tailWord_1321476) baseStart_1321476 baseEnd_1321476 := by
    simpa [prefixWord, tailWord_1321476, baseEnd_1321476] using wordTrace_append hprefix tailTrace_1321476
  have hstable : (prefixWord ++ tailWord_1321476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321476).length < 2 ^ (prefixWord ++ tailWord_1321476).sum := by decide
  have hdescent : baseEnd_1321476 < baseStart_1321476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321515 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 6, 2]
def baseStart_1321515 : Nat := 118140960795 + 1321515 * 2 ^ 59
def prefixEnd_1321515 : Nat := 4983230072969 + 3 ^ 40 * 1321515 * 2
def baseEnd_1321515 : Nat := 678572387126502300184969

theorem tailTrace_1321515 : CollatzResearch.WordTrace tailWord_1321515 prefixEnd_1321515 678572387126502300184969 := by
  unfold tailWord_1321515
  simp only [CollatzResearch.WordTrace]
  refine ⟨48199611807384326638469999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32133074538256217758979999 48199611807384326638469999)
  ·
    refine ⟨72299417711076489957704999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48199611807384326638469999 72299417711076489957704999)
    ·
      refine ⟨108449126566614734936557499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72299417711076489957704999 108449126566614734936557499)
      ·
        refine ⟨162673689849922102404836249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108449126566614734936557499 162673689849922102404836249)
        ·
          refine ⟨122005267387441576803627187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162673689849922102404836249 122005267387441576803627187)
          ·
            refine ⟨183007901081162365205440781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122005267387441576803627187 183007901081162365205440781)
            ·
              refine ⟨68627962905435886952040293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183007901081162365205440781 68627962905435886952040293)
              ·
                refine ⟨12867743044769228803507555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68627962905435886952040293 12867743044769228803507555)
                ·
                  refine ⟨19301614567153843205261333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12867743044769228803507555 19301614567153843205261333)
                  ·
                    refine ⟨904763182835336400246625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19301614567153843205261333 904763182835336400246625)
                    ·
                      refine ⟨678572387126502300184969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904763182835336400246625 678572387126502300184969)
                      ·
                        rfl

theorem cell23_1321515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6, 2].length) (baseStart_1321515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321515 prefixEnd_1321515 := by exact prefixLift 1321515
  have htrace : WordTrace (prefixWord ++ tailWord_1321515) baseStart_1321515 baseEnd_1321515 := by
    simpa [prefixWord, tailWord_1321515, baseEnd_1321515] using wordTrace_append hprefix tailTrace_1321515
  have hstable : (prefixWord ++ tailWord_1321515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321515).length < 2 ^ (prefixWord ++ tailWord_1321515).sum := by decide
  have hdescent : baseEnd_1321515 < baseStart_1321515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321532 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1321532 : Nat := 118140960795 + 1321532 * 2 ^ 59
def prefixEnd_1321532 : Nat := 4983230072969 + 3 ^ 40 * 1321532 * 2
def baseEnd_1321532 : Nat := 678581116297628733672391

theorem tailTrace_1321532 : CollatzResearch.WordTrace tailWord_1321532 prefixEnd_1321532 678581116297628733672391 := by
  unfold tailWord_1321532
  simp only [CollatzResearch.WordTrace]
  refine ⟨24100115924161369270919425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32133487898881825694559233 24100115924161369270919425)
  ·
    refine ⟨18075086943121026953189569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24100115924161369270919425 18075086943121026953189569)
    ·
      refine ⟨13556315207340770214892177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18075086943121026953189569 13556315207340770214892177)
      ·
        refine ⟨10167236405505577661169133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13556315207340770214892177 10167236405505577661169133)
        ·
          refine ⟨3812713652064591622938425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10167236405505577661169133 3812713652064591622938425)
          ·
            refine ⟨2859535239048443717203819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3812713652064591622938425 2859535239048443717203819)
            ·
              refine ⟨4289302858572665575805729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859535239048443717203819 4289302858572665575805729)
              ·
                refine ⟨3216977143929499181854297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4289302858572665575805729 3216977143929499181854297)
                ·
                  refine ⟨2412732857947124386390723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3216977143929499181854297 2412732857947124386390723)
                  ·
                    refine ⟨3619099286920686579586085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2412732857947124386390723 3619099286920686579586085)
                    ·
                      refine ⟨678581116297628733672391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3619099286920686579586085 678581116297628733672391)
                      ·
                        rfl

theorem cell23_1321532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1321532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321532 prefixEnd_1321532 := by exact prefixLift 1321532
  have htrace : WordTrace (prefixWord ++ tailWord_1321532) baseStart_1321532 baseEnd_1321532 := by
    simpa [prefixWord, tailWord_1321532, baseEnd_1321532] using wordTrace_append hprefix tailTrace_1321532
  have hstable : (prefixWord ++ tailWord_1321532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321532).length < 2 ^ (prefixWord ++ tailWord_1321532).sum := by decide
  have hdescent : baseEnd_1321532 < baseStart_1321532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321589 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 6]
def baseStart_1321589 : Nat := 118140960795 + 1321589 * 2 ^ 59
def prefixEnd_1321589 : Nat := 4983230072969 + 3 ^ 40 * 1321589 * 2
def baseEnd_1321589 : Nat := 75401153854992778962181

theorem tailTrace_1321589 : CollatzResearch.WordTrace tailWord_1321589 prefixEnd_1321589 75401153854992778962181 := by
  unfold tailWord_1321589
  simp only [CollatzResearch.WordTrace]
  refine ⟨48202310809116237276663821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32134873872744158184442547 48202310809116237276663821)
  ·
    refine ⟨18075866553418588978748933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48202310809116237276663821 18075866553418588978748933)
    ·
      refine ⟨3389224978765985433515425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18075866553418588978748933 3389224978765985433515425)
      ·
        refine ⟨2541918734074489075136569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3389224978765985433515425 2541918734074489075136569)
        ·
          refine ⟨1906439050555866806352427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2541918734074489075136569 1906439050555866806352427)
          ·
            refine ⟨2859658575833800209528641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906439050555866806352427 2859658575833800209528641)
            ·
              refine ⟨2144743931875350157146481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859658575833800209528641 2144743931875350157146481)
              ·
                refine ⟨1608557948906512617859861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2144743931875350157146481 1608557948906512617859861)
                ·
                  refine ⟨75401153854992778962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1608557948906512617859861 75401153854992778962181)
                  ·
                    rfl

theorem cell23_1321589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_1321589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321589 prefixEnd_1321589 := by exact prefixLift 1321589
  have htrace : WordTrace (prefixWord ++ tailWord_1321589) baseStart_1321589 baseEnd_1321589 := by
    simpa [prefixWord, tailWord_1321589, baseEnd_1321589] using wordTrace_append hprefix tailTrace_1321589
  have hstable : (prefixWord ++ tailWord_1321589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321589).length < 2 ^ (prefixWord ++ tailWord_1321589).sum := by decide
  have hdescent : baseEnd_1321589 < baseStart_1321589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321626 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1321626 : Nat := 118140960795 + 1321626 * 2 ^ 59
def prefixEnd_1321626 : Nat := 4983230072969 + 3 ^ 40 * 1321626 * 2
def baseEnd_1321626 : Nat := 678629383479151365896959

theorem tailTrace_1321626 : CollatzResearch.WordTrace tailWord_1321626 prefixEnd_1321626 678629383479151365896959 := by
  unfold tailWord_1321626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12050915077495548148940183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32135773539988128397173821 12050915077495548148940183)
  ·
    refine ⟨18076372616243322223410275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12050915077495548148940183 18076372616243322223410275)
    ·
      refine ⟨27114558924364983335115413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18076372616243322223410275 27114558924364983335115413)
      ·
        refine ⟨1270994949579608593833535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27114558924364983335115413 1270994949579608593833535)
        ·
          refine ⟨1906492424369412890750303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270994949579608593833535 1906492424369412890750303)
          ·
            refine ⟨2859738636554119336125455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906492424369412890750303 2859738636554119336125455)
            ·
              refine ⟨4289607954831179004188183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859738636554119336125455 4289607954831179004188183)
              ·
                refine ⟨6434411932246768506282275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289607954831179004188183 6434411932246768506282275)
                ·
                  refine ⟨9651617898370152759423413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6434411932246768506282275 9651617898370152759423413)
                  ·
                    refine ⟨904839177972201821195945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9651617898370152759423413 904839177972201821195945)
                    ·
                      refine ⟨678629383479151365896959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904839177972201821195945 678629383479151365896959)
                      ·
                        rfl

theorem cell23_1321626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1321626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321626 prefixEnd_1321626 := by exact prefixLift 1321626
  have htrace : WordTrace (prefixWord ++ tailWord_1321626) baseStart_1321626 baseEnd_1321626 := by
    simpa [prefixWord, tailWord_1321626, baseEnd_1321626] using wordTrace_append hprefix tailTrace_1321626
  have hstable : (prefixWord ++ tailWord_1321626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321626).length < 2 ^ (prefixWord ++ tailWord_1321626).sum := by decide
  have hdescent : baseEnd_1321626 < baseStart_1321626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321633 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_1321633 : Nat := 118140960795 + 1321633 * 2 ^ 59
def prefixEnd_1321633 : Nat := 4983230072969 + 3 ^ 40 * 1321633 * 2
def baseEnd_1321633 : Nat := 678632977843732838509427

theorem tailTrace_1321633 : CollatzResearch.WordTrace tailWord_1321633 prefixEnd_1321633 678632977843732838509427 := by
  unfold tailWord_1321633
  simp only [CollatzResearch.WordTrace]
  refine ⟨48203915620956832791265553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32135943747304555194177035 48203915620956832791265553)
  ·
    refine ⟨36152936715717624593449165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48203915620956832791265553 36152936715717624593449165)
    ·
      refine ⟨13557351268394109222543437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36152936715717624593449165 13557351268394109222543437)
      ·
        refine ⟨5084006725647790958453789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13557351268394109222543437 5084006725647790958453789)
        ·
          refine ⟨1906502522117921609420171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5084006725647790958453789 1906502522117921609420171)
          ·
            refine ⟨2859753783176882414130257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906502522117921609420171 2859753783176882414130257)
            ·
              refine ⟨2144815337382661810597693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859753783176882414130257 2144815337382661810597693)
              ·
                refine ⟨804305751518498178974135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2144815337382661810597693 804305751518498178974135)
                ·
                  refine ⟨1206458627277747268461203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804305751518498178974135 1206458627277747268461203)
                  ·
                    refine ⟨1809687940916620902691805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1206458627277747268461203 1809687940916620902691805)
                    ·
                      refine ⟨678632977843732838509427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1809687940916620902691805 678632977843732838509427)
                      ·
                        rfl

theorem cell23_1321633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_1321633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321633 prefixEnd_1321633 := by exact prefixLift 1321633
  have htrace : WordTrace (prefixWord ++ tailWord_1321633) baseStart_1321633 baseEnd_1321633 := by
    simpa [prefixWord, tailWord_1321633, baseEnd_1321633] using wordTrace_append hprefix tailTrace_1321633
  have hstable : (prefixWord ++ tailWord_1321633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321633).length < 2 ^ (prefixWord ++ tailWord_1321633).sum := by decide
  have hdescent : baseEnd_1321633 < baseStart_1321633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321635 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1321635 : Nat := 118140960795 + 1321635 * 2 ^ 59
def prefixEnd_1321635 : Nat := 4983230072969 + 3 ^ 40 * 1321635 * 2
def baseEnd_1321635 : Nat := 678634004805041830684417

theorem tailTrace_1321635 : CollatzResearch.WordTrace tailWord_1321635 prefixEnd_1321635 678634004805041830684417 := by
  unfold tailWord_1321635
  simp only [CollatzResearch.WordTrace]
  refine ⟨48203988566949587132838359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32135992377966391421892239 48203988566949587132838359)
  ·
    refine ⟨72305982850424380699257539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48203988566949587132838359 72305982850424380699257539)
    ·
      refine ⟨108458974275636571048886309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72305982850424380699257539 108458974275636571048886309)
      ·
        refine ⟨20336057676681857071666183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108458974275636571048886309 20336057676681857071666183)
        ·
          refine ⟨30504086515022785607499275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20336057676681857071666183 30504086515022785607499275)
          ·
            refine ⟨45756129772534178411248913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30504086515022785607499275 45756129772534178411248913)
            ·
              refine ⟨34317097329400633808436685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45756129772534178411248913 34317097329400633808436685)
              ·
                refine ⟨12868911498525237678163757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34317097329400633808436685 12868911498525237678163757)
                ·
                  refine ⟨4825841811946964129311409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12868911498525237678163757 4825841811946964129311409)
                  ·
                    refine ⟨3619381358960223096983557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4825841811946964129311409 3619381358960223096983557)
                    ·
                      refine ⟨678634004805041830684417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3619381358960223096983557 678634004805041830684417)
                      ·
                        rfl

theorem cell23_1321635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1321635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321635 prefixEnd_1321635 := by exact prefixLift 1321635
  have htrace : WordTrace (prefixWord ++ tailWord_1321635) baseStart_1321635 baseEnd_1321635 := by
    simpa [prefixWord, tailWord_1321635, baseEnd_1321635] using wordTrace_append hprefix tailTrace_1321635
  have hstable : (prefixWord ++ tailWord_1321635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321635).length < 2 ^ (prefixWord ++ tailWord_1321635).sum := by decide
  have hdescent : baseEnd_1321635 < baseStart_1321635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321676 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1321676 : Nat := 118140960795 + 1321676 * 2 ^ 59
def prefixEnd_1321676 : Nat := 4983230072969 + 3 ^ 40 * 1321676 * 2
def baseEnd_1321676 : Nat := 678655057511876170271729

theorem tailTrace_1321676 : CollatzResearch.WordTrace tailWord_1321676 prefixEnd_1321676 678655057511876170271729 := by
  unfold tailWord_1321676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24102741979900525567540441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32136989306534034090053921 24102741979900525567540441)
  ·
    refine ⟨18077056484925394175655331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24102741979900525567540441 18077056484925394175655331)
    ·
      refine ⟨27115584727388091263482997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18077056484925394175655331 27115584727388091263482997)
      ·
        refine ⟨2542086068192633555951531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27115584727388091263482997 2542086068192633555951531)
        ·
          refine ⟨3813129102288950333927297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542086068192633555951531 3813129102288950333927297)
          ·
            refine ⟨2859846826716712750445473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813129102288950333927297 2859846826716712750445473)
            ·
              refine ⟨2144885120037534562834105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859846826716712750445473 2144885120037534562834105)
              ·
                refine ⟨1608663840028150922125579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2144885120037534562834105 1608663840028150922125579)
                ·
                  refine ⟨2412995760042226383188369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608663840028150922125579 2412995760042226383188369)
                  ·
                    refine ⟨1809746820031669787391277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2412995760042226383188369 1809746820031669787391277)
                    ·
                      refine ⟨678655057511876170271729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1809746820031669787391277 678655057511876170271729)
                      ·
                        rfl

theorem cell23_1321676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1321676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321676 prefixEnd_1321676 := by exact prefixLift 1321676
  have htrace : WordTrace (prefixWord ++ tailWord_1321676) baseStart_1321676 baseEnd_1321676 := by
    simpa [prefixWord, tailWord_1321676, baseEnd_1321676] using wordTrace_append hprefix tailTrace_1321676
  have hstable : (prefixWord ++ tailWord_1321676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321676).length < 2 ^ (prefixWord ++ tailWord_1321676).sum := by decide
  have hdescent : baseEnd_1321676 < baseStart_1321676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321705 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_1321705 : Nat := 118140960795 + 1321705 * 2 ^ 59
def prefixEnd_1321705 : Nat := 4983230072969 + 3 ^ 40 * 1321705 * 2
def baseEnd_1321705 : Nat := 226223316150285518936365

theorem tailTrace_1321705 : CollatzResearch.WordTrace tailWord_1321705 prefixEnd_1321705 226223316150285518936365 := by
  unfold tailWord_1321705
  simp only [CollatzResearch.WordTrace]
  refine ⟨48206541676695989087886569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32137694451130659391924379 48206541676695989087886569)
  ·
    refine ⟨36154906257521991815914927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48206541676695989087886569 36154906257521991815914927)
    ·
      refine ⟨54232359386282987723872391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36154906257521991815914927 54232359386282987723872391)
      ·
        refine ⟨81348539079424481585808587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54232359386282987723872391 81348539079424481585808587)
        ·
          refine ⟨122022808619136722378712881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81348539079424481585808587 122022808619136722378712881)
          ·
            refine ⟨91517106464352541784034661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122022808619136722378712881 91517106464352541784034661)
            ·
              refine ⟨17159457462066101584506499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91517106464352541784034661 17159457462066101584506499)
              ·
                refine ⟨25739186193099152376759749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17159457462066101584506499 25739186193099152376759749)
                ·
                  refine ⟨4826097411206091070642453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25739186193099152376759749 4826097411206091070642453)
                  ·
                    refine ⟨226223316150285518936365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4826097411206091070642453 226223316150285518936365)
                    ·
                      rfl

theorem cell23_1321705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_1321705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321705 prefixEnd_1321705 := by exact prefixLift 1321705
  have htrace : WordTrace (prefixWord ++ tailWord_1321705) baseStart_1321705 baseEnd_1321705 := by
    simpa [prefixWord, tailWord_1321705, baseEnd_1321705] using wordTrace_append hprefix tailTrace_1321705
  have hstable : (prefixWord ++ tailWord_1321705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321705).length < 2 ^ (prefixWord ++ tailWord_1321705).sum := by decide
  have hdescent : baseEnd_1321705 < baseStart_1321705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321715 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_1321715 : Nat := 118140960795 + 1321715 * 2 ^ 59
def prefixEnd_1321715 : Nat := 4983230072969 + 3 ^ 40 * 1321715 * 2
def baseEnd_1321715 : Nat := 678675083257401517684049

theorem tailTrace_1321715 : CollatzResearch.WordTrace tailWord_1321715 prefixEnd_1321715 678675083257401517684049 := by
  unfold tailWord_1321715
  simp only [CollatzResearch.WordTrace]
  refine ⟨48206906406659760795750599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32137937604439840530500399 48206906406659760795750599)
  ·
    refine ⟨72310359609989641193625899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48206906406659760795750599 72310359609989641193625899)
    ·
      refine ⟨108465539414984461790438849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72310359609989641193625899 108465539414984461790438849)
      ·
        refine ⟨81349154561238346342829137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108465539414984461790438849 81349154561238346342829137)
        ·
          refine ⟨61011865920928759757121853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81349154561238346342829137 61011865920928759757121853)
          ·
            refine ⟨22879449720348284908920695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61011865920928759757121853 22879449720348284908920695)
            ·
              refine ⟨34319174580522427363381043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22879449720348284908920695 34319174580522427363381043)
              ·
                refine ⟨51478761870783641045071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34319174580522427363381043 51478761870783641045071565)
                ·
                  refine ⟨19304535701543865391901837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51478761870783641045071565 19304535701543865391901837)
                  ·
                    refine ⟨7239200888078949521963189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19304535701543865391901837 7239200888078949521963189)
                    ·
                      refine ⟨678675083257401517684049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7239200888078949521963189 678675083257401517684049)
                      ·
                        rfl

theorem cell23_1321715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_1321715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321715 prefixEnd_1321715 := by exact prefixLift 1321715
  have htrace : WordTrace (prefixWord ++ tailWord_1321715) baseStart_1321715 baseEnd_1321715 := by
    simpa [prefixWord, tailWord_1321715, baseEnd_1321715] using wordTrace_append hprefix tailTrace_1321715
  have hstable : (prefixWord ++ tailWord_1321715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321715).length < 2 ^ (prefixWord ++ tailWord_1321715).sum := by decide
  have hdescent : baseEnd_1321715 < baseStart_1321715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321717 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1321717 : Nat := 118140960795 + 1321717 * 2 ^ 59
def prefixEnd_1321717 : Nat := 4983230072969 + 3 ^ 40 * 1321717 * 2
def baseEnd_1321717 : Nat := 226225370072903503286347

theorem tailTrace_1321717 : CollatzResearch.WordTrace tailWord_1321717 prefixEnd_1321717 226225370072903503286347 := by
  unfold tailWord_1321717
  simp only [CollatzResearch.WordTrace]
  refine ⟨48206979352652515137323405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32137986235101676758215603 48206979352652515137323405)
  ·
    refine ⟨18077617257244693176496277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48206979352652515137323405 18077617257244693176496277)
    ·
      refine ⟨847388308933344992648263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18077617257244693176496277 847388308933344992648263)
      ·
        refine ⟨1271082463400017488972395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847388308933344992648263 1271082463400017488972395)
        ·
          refine ⟨1906623695100026233458593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271082463400017488972395 1906623695100026233458593)
          ·
            refine ⟨1429967771325019675093945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1906623695100026233458593 1429967771325019675093945)
            ·
              refine ⟨1072475828493764756320459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429967771325019675093945 1072475828493764756320459)
              ·
                refine ⟨1608713742740647134480689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072475828493764756320459 1608713742740647134480689)
                ·
                  refine ⟨1206535307055485350860517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1608713742740647134480689 1206535307055485350860517)
                  ·
                    refine ⟨226225370072903503286347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1206535307055485350860517 226225370072903503286347)
                    ·
                      rfl

theorem cell23_1321717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1321717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321717 prefixEnd_1321717 := by exact prefixLift 1321717
  have htrace : WordTrace (prefixWord ++ tailWord_1321717) baseStart_1321717 baseEnd_1321717 := by
    simpa [prefixWord, tailWord_1321717, baseEnd_1321717] using wordTrace_append hprefix tailTrace_1321717
  have hstable : (prefixWord ++ tailWord_1321717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321717).length < 2 ^ (prefixWord ++ tailWord_1321717).sum := by decide
  have hdescent : baseEnd_1321717 < baseStart_1321717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321729 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_1321729 : Nat := 118140960795 + 1321729 * 2 ^ 59
def prefixEnd_1321729 : Nat := 4983230072969 + 3 ^ 40 * 1321729 * 2
def baseEnd_1321729 : Nat := 678682271986564462908985

theorem tailTrace_1321729 : CollatzResearch.WordTrace tailWord_1321729 prefixEnd_1321729 678682271986564462908985 := by
  unfold tailWord_1321729
  simp only [CollatzResearch.WordTrace]
  refine ⟨48207417028609041186760241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32138278019072694124506827 48207417028609041186760241)
  ·
    refine ⟨36155562771456780890070181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48207417028609041186760241 36155562771456780890070181)
    ·
      refine ⟨6779168019648146416888159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36155562771456780890070181 6779168019648146416888159)
      ·
        refine ⟨10168752029472219625332239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6779168019648146416888159 10168752029472219625332239)
        ·
          refine ⟨15253128044208329437998359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10168752029472219625332239 15253128044208329437998359)
          ·
            refine ⟨22879692066312494156997539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15253128044208329437998359 22879692066312494156997539)
            ·
              refine ⟨34319538099468741235496309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22879692066312494156997539 34319538099468741235496309)
              ·
                refine ⟨3217456696825194490827779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34319538099468741235496309 3217456696825194490827779)
                ·
                  refine ⟨4826185045237791736241669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217456696825194490827779 4826185045237791736241669)
                  ·
                    refine ⟨904909695982085950545313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826185045237791736241669 904909695982085950545313)
                    ·
                      refine ⟨678682271986564462908985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 904909695982085950545313 678682271986564462908985)
                      ·
                        rfl

theorem cell23_1321729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_1321729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321729 prefixEnd_1321729 := by exact prefixLift 1321729
  have htrace : WordTrace (prefixWord ++ tailWord_1321729) baseStart_1321729 baseEnd_1321729 := by
    simpa [prefixWord, tailWord_1321729, baseEnd_1321729] using wordTrace_append hprefix tailTrace_1321729
  have hstable : (prefixWord ++ tailWord_1321729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321729).length < 2 ^ (prefixWord ++ tailWord_1321729).sum := by decide
  have hdescent : baseEnd_1321729 < baseStart_1321729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321732 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1321732 : Nat := 118140960795 + 1321732 * 2 ^ 59
def prefixEnd_1321732 : Nat := 4983230072969 + 3 ^ 40 * 1321732 * 2
def baseEnd_1321732 : Nat := 678683812428527951171471

theorem tailTrace_1321732 : CollatzResearch.WordTrace tailWord_1321732 prefixEnd_1321732 678683812428527951171471 := by
  unfold tailWord_1321732
  simp only [CollatzResearch.WordTrace]
  refine ⟨24103763223799086349559725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32138350965065448466079633 24103763223799086349559725)
  ·
    refine ⟨9038911208924657381084897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24103763223799086349559725 9038911208924657381084897)
    ·
      refine ⟨6779183406693493035813673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9038911208924657381084897 6779183406693493035813673)
      ·
        refine ⟨5084387555020119776860255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6779183406693493035813673 5084387555020119776860255)
        ·
          refine ⟨7626581332530179665290383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5084387555020119776860255 7626581332530179665290383)
          ·
            refine ⟨11439871998795269497935575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7626581332530179665290383 11439871998795269497935575)
            ·
              refine ⟨17159807998192904246903363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11439871998795269497935575 17159807998192904246903363)
              ·
                refine ⟨25739711997289356370355045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17159807998192904246903363 25739711997289356370355045)
                ·
                  refine ⟨4826195999491754319441571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25739711997289356370355045 4826195999491754319441571)
                  ·
                    refine ⟨7239293999237631479162357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826195999491754319441571 7239293999237631479162357)
                    ·
                      refine ⟨678683812428527951171471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7239293999237631479162357 678683812428527951171471)
                      ·
                        rfl

theorem cell23_1321732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1321732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321732 prefixEnd_1321732 := by exact prefixLift 1321732
  have htrace : WordTrace (prefixWord ++ tailWord_1321732) baseStart_1321732 baseEnd_1321732 := by
    simpa [prefixWord, tailWord_1321732, baseEnd_1321732] using wordTrace_append hprefix tailTrace_1321732
  have hstable : (prefixWord ++ tailWord_1321732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321732).length < 2 ^ (prefixWord ++ tailWord_1321732).sum := by decide
  have hdescent : baseEnd_1321732 < baseStart_1321732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321742 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1321742 : Nat := 118140960795 + 1321742 * 2 ^ 59
def prefixEnd_1321742 : Nat := 4983230072969 + 3 ^ 40 * 1321742 * 2
def baseEnd_1321742 : Nat := 678688947235072912046425

theorem tailTrace_1321742 : CollatzResearch.WordTrace tailWord_1321742 prefixEnd_1321742 678688947235072912046425 := by
  unfold tailWord_1321742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025986397195243050872935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32138594118374629604655653 6025986397195243050872935)
  ·
    refine ⟨9038979595792864576309403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6025986397195243050872935 9038979595792864576309403)
    ·
      refine ⟨13558469393689296864464105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9038979595792864576309403 13558469393689296864464105)
      ·
        refine ⟨10168852045266972648348079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13558469393689296864464105 10168852045266972648348079)
        ·
          refine ⟨15253278067900458972522119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10168852045266972648348079 15253278067900458972522119)
          ·
            refine ⟨22879917101850688458783179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15253278067900458972522119 22879917101850688458783179)
            ·
              refine ⟨34319875652776032688174769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22879917101850688458783179 34319875652776032688174769)
              ·
                refine ⟨25739906739582024516131077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34319875652776032688174769 25739906739582024516131077)
                ·
                  refine ⟨4826232513671629596774577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25739906739582024516131077 4826232513671629596774577)
                  ·
                    refine ⟨3619674385253722197580933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4826232513671629596774577 3619674385253722197580933)
                    ·
                      refine ⟨678688947235072912046425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3619674385253722197580933 678688947235072912046425)
                      ·
                        rfl

theorem cell23_1321742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1321742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321742 prefixEnd_1321742 := by exact prefixLift 1321742
  have htrace : WordTrace (prefixWord ++ tailWord_1321742) baseStart_1321742 baseEnd_1321742 := by
    simpa [prefixWord, tailWord_1321742, baseEnd_1321742] using wordTrace_append hprefix tailTrace_1321742
  have hstable : (prefixWord ++ tailWord_1321742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321742).length < 2 ^ (prefixWord ++ tailWord_1321742).sum := by decide
  have hdescent : baseEnd_1321742 < baseStart_1321742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321755 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_1321755 : Nat := 118140960795 + 1321755 * 2 ^ 59
def prefixEnd_1321755 : Nat := 4983230072969 + 3 ^ 40 * 1321755 * 2
def baseEnd_1321755 : Nat := 678695622483581361183865

theorem tailTrace_1321755 : CollatzResearch.WordTrace tailWord_1321755 prefixEnd_1321755 678695622483581361183865 := by
  unfold tailWord_1321755
  simp only [CollatzResearch.WordTrace]
  refine ⟨48208365326514847627206719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32138910217676565084804479 48208365326514847627206719)
  ·
    refine ⟨72312547989772271440810079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48208365326514847627206719 72312547989772271440810079)
    ·
      refine ⟨108468821984658407161215119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72312547989772271440810079 108468821984658407161215119)
      ·
        refine ⟨162703232976987610741822679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108468821984658407161215119 162703232976987610741822679)
        ·
          refine ⟨244054849465481416112734019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162703232976987610741822679 244054849465481416112734019)
          ·
            refine ⟨366082274198222124169101029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244054849465481416112734019 366082274198222124169101029)
            ·
              refine ⟨68640426412166648281706443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366082274198222124169101029 68640426412166648281706443)
              ·
                refine ⟨102960639618249972422559665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68640426412166648281706443 102960639618249972422559665)
                ·
                  refine ⟨77220479713687479316919749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102960639618249972422559665 77220479713687479316919749)
                  ·
                    refine ⟨14478839946316402371922453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77220479713687479316919749 14478839946316402371922453)
                    ·
                      refine ⟨678695622483581361183865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14478839946316402371922453 678695622483581361183865)
                      ·
                        rfl

theorem cell23_1321755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_1321755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321755 prefixEnd_1321755 := by exact prefixLift 1321755
  have htrace : WordTrace (prefixWord ++ tailWord_1321755) baseStart_1321755 baseEnd_1321755 := by
    simpa [prefixWord, tailWord_1321755, baseEnd_1321755] using wordTrace_append hprefix tailTrace_1321755
  have hstable : (prefixWord ++ tailWord_1321755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321755).length < 2 ^ (prefixWord ++ tailWord_1321755).sum := by decide
  have hdescent : baseEnd_1321755 < baseStart_1321755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321779 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 3]
def baseStart_1321779 : Nat := 118140960795 + 1321779 * 2 ^ 59
def prefixEnd_1321779 : Nat := 4983230072969 + 3 ^ 40 * 1321779 * 2
def baseEnd_1321779 : Nat := 678707946019289267283755

theorem tailTrace_1321779 : CollatzResearch.WordTrace tailWord_1321779 prefixEnd_1321779 678707946019289267283755 := by
  unfold tailWord_1321779
  simp only [CollatzResearch.WordTrace]
  refine ⟨48209240678427899726080391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32139493785618599817386927 48209240678427899726080391)
  ·
    refine ⟨72313861017641849589120587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48209240678427899726080391 72313861017641849589120587)
    ·
      refine ⟨108470791526462774383680881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72313861017641849589120587 108470791526462774383680881)
      ·
        refine ⟨81353093644847080787760661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108470791526462774383680881 81353093644847080787760661)
        ·
          refine ⟨3813426264602206911926281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81353093644847080787760661 3813426264602206911926281)
          ·
            refine ⟨2860069698451655183944711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813426264602206911926281 2860069698451655183944711)
            ·
              refine ⟨4290104547677482775917067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860069698451655183944711 4290104547677482775917067)
              ·
                refine ⟨6435156821516224163875601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290104547677482775917067 6435156821516224163875601)
                ·
                  refine ⟨4826367616137168122906701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435156821516224163875601 4826367616137168122906701)
                  ·
                    refine ⟨1809887856051438046090013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4826367616137168122906701 1809887856051438046090013)
                    ·
                      refine ⟨678707946019289267283755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1809887856051438046090013 678707946019289267283755)
                      ·
                        rfl

theorem cell23_1321779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_1321779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321779 prefixEnd_1321779 := by exact prefixLift 1321779
  have htrace : WordTrace (prefixWord ++ tailWord_1321779) baseStart_1321779 baseEnd_1321779 := by
    simpa [prefixWord, tailWord_1321779, baseEnd_1321779] using wordTrace_append hprefix tailTrace_1321779
  have hstable : (prefixWord ++ tailWord_1321779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321779).length < 2 ^ (prefixWord ++ tailWord_1321779).sum := by decide
  have hdescent : baseEnd_1321779 < baseStart_1321779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321829 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_1321829 : Nat := 118140960795 + 1321829 * 2 ^ 59
def prefixEnd_1321829 : Nat := 4983230072969 + 3 ^ 40 * 1321829 * 2
def baseEnd_1321829 : Nat := 226244540017338023886175

theorem tailTrace_1321829 : CollatzResearch.WordTrace tailWord_1321829 prefixEnd_1321829 226244540017338023886175 := by
  unfold tailWord_1321829
  simp only [CollatzResearch.WordTrace]
  refine ⟨48211064328246758265400541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32140709552164505510267027 48211064328246758265400541)
  ·
    refine ⟨18079149123092534349525203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48211064328246758265400541 18079149123092534349525203)
    ·
      refine ⟨27118723684638801524287805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18079149123092534349525203 27118723684638801524287805)
      ·
        refine ⟨10169521381739550571607927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27118723684638801524287805 10169521381739550571607927)
        ·
          refine ⟨15254282072609325857411891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10169521381739550571607927 15254282072609325857411891)
          ·
            refine ⟨22881423108913988786117837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15254282072609325857411891 22881423108913988786117837)
            ·
              refine ⟨8580533665842745794794189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22881423108913988786117837 8580533665842745794794189)
              ·
                refine ⟨3217700124691029673047821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8580533665842745794794189 3217700124691029673047821)
                ·
                  refine ⟨1206637546759136127392933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3217700124691029673047821 1206637546759136127392933)
                  ·
                    refine ⟨226244540017338023886175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1206637546759136127392933 226244540017338023886175)
                    ·
                      rfl

theorem cell23_1321829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_1321829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321829 prefixEnd_1321829 := by exact prefixLift 1321829
  have htrace : WordTrace (prefixWord ++ tailWord_1321829) baseStart_1321829 baseEnd_1321829 := by
    simpa [prefixWord, tailWord_1321829, baseEnd_1321829] using wordTrace_append hprefix tailTrace_1321829
  have hstable : (prefixWord ++ tailWord_1321829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321829).length < 2 ^ (prefixWord ++ tailWord_1321829).sum := by decide
  have hdescent : baseEnd_1321829 < baseStart_1321829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321863 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 1, 4]
def baseStart_1321863 : Nat := 118140960795 + 1321863 * 2 ^ 59
def prefixEnd_1321863 : Nat := 4983230072969 + 3 ^ 40 * 1321863 * 2
def baseEnd_1321863 : Nat := 226250359464755646211123

theorem tailTrace_1321863 : CollatzResearch.WordTrace tailWord_1321863 prefixEnd_1321863 226250359464755646211123 := by
  unfold tailWord_1321863
  simp only [CollatzResearch.WordTrace]
  refine ⟨48212304410123582072138243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32141536273415721381425495 48212304410123582072138243)
  ·
    refine ⟨72318456615185373108207365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48212304410123582072138243 72318456615185373108207365)
    ·
      refine ⟨13559710615347257457788881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72318456615185373108207365 13559710615347257457788881)
      ·
        refine ⟨10169782961510443093341661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13559710615347257457788881 10169782961510443093341661)
        ·
          refine ⟨3813668610566416160003123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10169782961510443093341661 3813668610566416160003123)
          ·
            refine ⟨5720502915849624240004685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3813668610566416160003123 5720502915849624240004685)
            ·
              refine ⟨2145188593443609090001757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5720502915849624240004685 2145188593443609090001757)
              ·
                refine ⟨804445722541353408750659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2145188593443609090001757 804445722541353408750659)
                ·
                  refine ⟨1206668583812030113125989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804445722541353408750659 1206668583812030113125989)
                  ·
                    refine ⟨226250359464755646211123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1206668583812030113125989 226250359464755646211123)
                    ·
                      rfl

theorem cell23_1321863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_1321863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321863 prefixEnd_1321863 := by exact prefixLift 1321863
  have htrace : WordTrace (prefixWord ++ tailWord_1321863) baseStart_1321863 baseEnd_1321863 := by
    simpa [prefixWord, tailWord_1321863, baseEnd_1321863] using wordTrace_append hprefix tailTrace_1321863
  have hstable : (prefixWord ++ tailWord_1321863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321863).length < 2 ^ (prefixWord ++ tailWord_1321863).sum := by decide
  have hdescent : baseEnd_1321863 < baseStart_1321863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321913 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1321913 : Nat := 118140960795 + 1321913 * 2 ^ 59
def prefixEnd_1321913 : Nat := 4983230072969 + 3 ^ 40 * 1321913 * 2
def baseEnd_1321913 : Nat := 678776752426991743008139

theorem tailTrace_1321913 : CollatzResearch.WordTrace tailWord_1321913 prefixEnd_1321913 678776752426991743008139 := by
  unfold tailWord_1321913
  simp only [CollatzResearch.WordTrace]
  refine ⟨48214128059942440611458393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32142752039961627074305595 48214128059942440611458393)
  ·
    refine ⟨36160596044956830458593795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48214128059942440611458393 36160596044956830458593795)
    ·
      refine ⟨54240894067435245687890693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36160596044956830458593795 54240894067435245687890693)
      ·
        refine ⟨10170167637644108566479505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54240894067435245687890693 10170167637644108566479505)
        ·
          refine ⟨7627625728233081424859629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10170167637644108566479505 7627625728233081424859629)
          ·
            refine ⟨2860359648087405534322361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7627625728233081424859629 2860359648087405534322361)
            ·
              refine ⟨2145269736065554150741771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860359648087405534322361 2145269736065554150741771)
              ·
                refine ⟨3217904604098331226112657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145269736065554150741771 3217904604098331226112657)
                ·
                  refine ⟨2413428453073748419584493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3217904604098331226112657 2413428453073748419584493)
                  ·
                    refine ⟨905035669902655657344185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413428453073748419584493 905035669902655657344185)
                    ·
                      refine ⟨678776752426991743008139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905035669902655657344185 678776752426991743008139)
                      ·
                        rfl

theorem cell23_1321913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1321913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321913 prefixEnd_1321913 := by exact prefixLift 1321913
  have htrace : WordTrace (prefixWord ++ tailWord_1321913) baseStart_1321913 baseEnd_1321913 := by
    simpa [prefixWord, tailWord_1321913, baseEnd_1321913] using wordTrace_append hprefix tailTrace_1321913
  have hstable : (prefixWord ++ tailWord_1321913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321913).length < 2 ^ (prefixWord ++ tailWord_1321913).sum := by decide
  have hdescent : baseEnd_1321913 < baseStart_1321913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321919 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 4, 4]
def baseStart_1321919 : Nat := 118140960795 + 1321919 * 2 ^ 59
def prefixEnd_1321919 : Nat := 4983230072969 + 3 ^ 40 * 1321919 * 2
def baseEnd_1321919 : Nat := 226259944436972906511037

theorem tailTrace_1321919 : CollatzResearch.WordTrace tailWord_1321919 prefixEnd_1321919 226259944436972906511037 := by
  unfold tailWord_1321919
  simp only [CollatzResearch.WordTrace]
  refine ⟨48214346897920703636176811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32142897931947135757451207 48214346897920703636176811)
  ·
    refine ⟨72321520346881055454265217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48214346897920703636176811 72321520346881055454265217)
    ·
      refine ⟨54241140260160791590698913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72321520346881055454265217 54241140260160791590698913)
      ·
        refine ⟨40680855195120593693024185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54241140260160791590698913 40680855195120593693024185)
        ·
          refine ⟨30510641396340445269768139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40680855195120593693024185 30510641396340445269768139)
          ·
            refine ⟨45765962094510667904652209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30510641396340445269768139 45765962094510667904652209)
            ·
              refine ⟨34324471570883000928489157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45765962094510667904652209 34324471570883000928489157)
              ·
                refine ⟨6435838419540562674091717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34324471570883000928489157 6435838419540562674091717)
                ·
                  refine ⟨1206719703663855501392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6435838419540562674091717 1206719703663855501392197)
                  ·
                    refine ⟨226259944436972906511037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1206719703663855501392197 226259944436972906511037)
                    ·
                      rfl

theorem cell23_1321919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_1321919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321919 prefixEnd_1321919 := by exact prefixLift 1321919
  have htrace : WordTrace (prefixWord ++ tailWord_1321919) baseStart_1321919 baseEnd_1321919 := by
    simpa [prefixWord, tailWord_1321919, baseEnd_1321919] using wordTrace_append hprefix tailTrace_1321919
  have hstable : (prefixWord ++ tailWord_1321919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321919).length < 2 ^ (prefixWord ++ tailWord_1321919).sum := by decide
  have hdescent : baseEnd_1321919 < baseStart_1321919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321929 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_1321929 : Nat := 118140960795 + 1321929 * 2 ^ 59
def prefixEnd_1321929 : Nat := 4983230072969 + 3 ^ 40 * 1321929 * 2
def baseEnd_1321929 : Nat := 678784968117463680408065

theorem tailTrace_1321929 : CollatzResearch.WordTrace tailWord_1321929 prefixEnd_1321929 678784968117463680408065 := by
  unfold tailWord_1321929
  simp only [CollatzResearch.WordTrace]
  refine ⟨48214711627884475344040841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32143141085256316896027227 48214711627884475344040841)
  ·
    refine ⟨36161033720913356508030631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48214711627884475344040841 36161033720913356508030631)
    ·
      refine ⟨54241550581370034762045947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36161033720913356508030631 54241550581370034762045947)
      ·
        refine ⟨81362325872055052143068921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54241550581370034762045947 81362325872055052143068921)
        ·
          refine ⟨61021744404041289107301691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81362325872055052143068921 61021744404041289107301691)
          ·
            refine ⟨91532616606061933660952537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61021744404041289107301691 91532616606061933660952537)
            ·
              refine ⟨68649462454546450245714403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91532616606061933660952537 68649462454546450245714403)
              ·
                refine ⟨102974193681819675368571605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68649462454546450245714403 102974193681819675368571605)
                ·
                  refine ⟨2413457664417648641450897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 102974193681819675368571605 2413457664417648641450897)
                  ·
                    refine ⟨1810093248313236481088173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2413457664417648641450897 1810093248313236481088173)
                    ·
                      refine ⟨678784968117463680408065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810093248313236481088173 678784968117463680408065)
                      ·
                        rfl

theorem cell23_1321929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_1321929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321929 prefixEnd_1321929 := by exact prefixLift 1321929
  have htrace : WordTrace (prefixWord ++ tailWord_1321929) baseStart_1321929 baseEnd_1321929 := by
    simpa [prefixWord, tailWord_1321929, baseEnd_1321929] using wordTrace_append hprefix tailTrace_1321929
  have hstable : (prefixWord ++ tailWord_1321929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321929).length < 2 ^ (prefixWord ++ tailWord_1321929).sum := by decide
  have hdescent : baseEnd_1321929 < baseStart_1321929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321946 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_1321946 : Nat := 118140960795 + 1321946 * 2 ^ 59
def prefixEnd_1321946 : Nat := 4983230072969 + 3 ^ 40 * 1321946 * 2
def baseEnd_1321946 : Nat := 678793697288590113895487

theorem tailTrace_1321946 : CollatzResearch.WordTrace tailWord_1321946 prefixEnd_1321946 678793697288590113895487 := by
  unfold tailWord_1321946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053832917205721811852423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32143554445881924831606461 12053832917205721811852423)
  ·
    refine ⟨18080749375808582717778635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12053832917205721811852423 18080749375808582717778635)
    ·
      refine ⟨27121124063712874076667953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18080749375808582717778635 27121124063712874076667953)
      ·
        refine ⟨20340843047784655557500965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27121124063712874076667953 20340843047784655557500965)
        ·
          refine ⟨3813908071459622917031431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20340843047784655557500965 3813908071459622917031431)
          ·
            refine ⟨5720862107189434375547147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3813908071459622917031431 5720862107189434375547147)
            ·
              refine ⟨8581293160784151563320721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5720862107189434375547147 8581293160784151563320721)
              ·
                refine ⟨6435969870588113672490541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8581293160784151563320721 6435969870588113672490541)
                ·
                  refine ⟨2413488701470542627183953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6435969870588113672490541 2413488701470542627183953)
                  ·
                    refine ⟨1810116526102906970387965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2413488701470542627183953 1810116526102906970387965)
                    ·
                      refine ⟨678793697288590113895487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810116526102906970387965 678793697288590113895487)
                      ·
                        rfl

theorem cell23_1321946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_1321946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321946 prefixEnd_1321946 := by exact prefixLift 1321946
  have htrace : WordTrace (prefixWord ++ tailWord_1321946) baseStart_1321946 baseEnd_1321946 := by
    simpa [prefixWord, tailWord_1321946, baseEnd_1321946] using wordTrace_append hprefix tailTrace_1321946
  have hstable : (prefixWord ++ tailWord_1321946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321946).length < 2 ^ (prefixWord ++ tailWord_1321946).sum := by decide
  have hdescent : baseEnd_1321946 < baseStart_1321946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321976 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_1321976 : Nat := 118140960795 + 1321976 * 2 ^ 59
def prefixEnd_1321976 : Nat := 4983230072969 + 3 ^ 40 * 1321976 * 2
def baseEnd_1321976 : Nat := 678809101708224996520349

theorem tailTrace_1321976 : CollatzResearch.WordTrace tailWord_1321976 prefixEnd_1321976 678809101708224996520349 := by
  unfold tailWord_1321976
  simp only [CollatzResearch.WordTrace]
  refine ⟨24108212929357101185500891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32144283905809468247334521 24108212929357101185500891)
  ·
    refine ⟨36162319394035651778251337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24108212929357101185500891 36162319394035651778251337)
    ·
      refine ⟨27121739545526738833688503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36162319394035651778251337 27121739545526738833688503)
      ·
        refine ⟨40682609318290108250532755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27121739545526738833688503 40682609318290108250532755)
        ·
          refine ⟨61023913977435162375799133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40682609318290108250532755 61023913977435162375799133)
          ·
            refine ⟨22883967741538185890924675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61023913977435162375799133 22883967741538185890924675)
            ·
              refine ⟨34325951612307278836387013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22883967741538185890924675 34325951612307278836387013)
              ·
                refine ⟨6436115927307614781822565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34325951612307278836387013 6436115927307614781822565)
                ·
                  refine ⟨1206771736370177771591731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6436115927307614781822565 1206771736370177771591731)
                  ·
                    refine ⟨1810157604555266657387597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1206771736370177771591731 1810157604555266657387597)
                    ·
                      refine ⟨678809101708224996520349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810157604555266657387597 678809101708224996520349)
                      ·
                        rfl

theorem cell23_1321976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_1321976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321976 prefixEnd_1321976 := by exact prefixLift 1321976
  have htrace : WordTrace (prefixWord ++ tailWord_1321976) baseStart_1321976 baseEnd_1321976 := by
    simpa [prefixWord, tailWord_1321976, baseEnd_1321976] using wordTrace_append hprefix tailTrace_1321976
  have hstable : (prefixWord ++ tailWord_1321976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321976).length < 2 ^ (prefixWord ++ tailWord_1321976).sum := by decide
  have hdescent : baseEnd_1321976 < baseStart_1321976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321980 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_1321980 : Nat := 118140960795 + 1321980 * 2 ^ 59
def prefixEnd_1321980 : Nat := 4983230072969 + 3 ^ 40 * 1321980 * 2
def baseEnd_1321980 : Nat := 678811155630842980870331

theorem tailTrace_1321980 : CollatzResearch.WordTrace tailWord_1321980 prefixEnd_1321980 678811155630842980870331 := by
  unfold tailWord_1321980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24108285875349855527073697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32144381167133140702764929 24108285875349855527073697)
  ·
    refine ⟨18081214406512391645305273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24108285875349855527073697 18081214406512391645305273)
    ·
      refine ⟨13560910804884293733978955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18081214406512391645305273 13560910804884293733978955)
      ·
        refine ⟨20341366207326440600968433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13560910804884293733978955 20341366207326440600968433)
        ·
          refine ⟨15256024655494830450726325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20341366207326440600968433 15256024655494830450726325)
          ·
            refine ⟨1430252311452640354755593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15256024655494830450726325 1430252311452640354755593)
            ·
              refine ⟨1072689233589480266066695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430252311452640354755593 1072689233589480266066695)
              ·
                refine ⟨1609033850384220399100043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072689233589480266066695 1609033850384220399100043)
                ·
                  refine ⟨2413550775576330598650065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609033850384220399100043 2413550775576330598650065)
                  ·
                    refine ⟨1810163081682247948987549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2413550775576330598650065 1810163081682247948987549)
                    ·
                      refine ⟨678811155630842980870331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810163081682247948987549 678811155630842980870331)
                      ·
                        rfl

theorem cell23_1321980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_1321980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1321980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1321980 prefixEnd_1321980 := by exact prefixLift 1321980
  have htrace : WordTrace (prefixWord ++ tailWord_1321980) baseStart_1321980 baseEnd_1321980 := by
    simpa [prefixWord, tailWord_1321980, baseEnd_1321980] using wordTrace_append hprefix tailTrace_1321980
  have hstable : (prefixWord ++ tailWord_1321980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321980).length < 2 ^ (prefixWord ++ tailWord_1321980).sum := by decide
  have hdescent : baseEnd_1321980 < baseStart_1321980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322009 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_1322009 : Nat := 118140960795 + 1322009 * 2 ^ 59
def prefixEnd_1322009 : Nat := 4983230072969 + 3 ^ 40 * 1322009 * 2
def baseEnd_1322009 : Nat := 226275348856607789135899

theorem tailTrace_1322009 : CollatzResearch.WordTrace tailWord_1322009 prefixEnd_1322009 226275348856607789135899 := by
  unfold tailWord_1322009
  simp only [CollatzResearch.WordTrace]
  refine ⟨48217629467594649006953081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32145086311729766004635387 48217629467594649006953081)
  ·
    refine ⟨36163222100695986755214811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48217629467594649006953081 36163222100695986755214811)
    ·
      refine ⟨54244833151043980132822217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36163222100695986755214811 54244833151043980132822217)
      ·
        refine ⟨40683624863282985099616663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54244833151043980132822217 40683624863282985099616663)
        ·
          refine ⟨61025437294924477649424995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40683624863282985099616663 61025437294924477649424995)
          ·
            refine ⟨91538155942386716474137493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61025437294924477649424995 91538155942386716474137493)
            ·
              refine ⟨4290851059799377334725195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91538155942386716474137493 4290851059799377334725195)
              ·
                refine ⟨6436276589699066002087793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290851059799377334725195 6436276589699066002087793)
                ·
                  refine ⟨4827207442274299501565845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6436276589699066002087793 4827207442274299501565845)
                  ·
                    refine ⟨226275348856607789135899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4827207442274299501565845 226275348856607789135899)
                    ·
                      rfl

theorem cell23_1322009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_1322009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322009 prefixEnd_1322009 := by exact prefixLift 1322009
  have htrace : WordTrace (prefixWord ++ tailWord_1322009) baseStart_1322009 baseEnd_1322009 := by
    simpa [prefixWord, tailWord_1322009, baseEnd_1322009] using wordTrace_append hprefix tailTrace_1322009
  have hstable : (prefixWord ++ tailWord_1322009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322009).length < 2 ^ (prefixWord ++ tailWord_1322009).sum := by decide
  have hdescent : baseEnd_1322009 < baseStart_1322009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322010 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3]
def baseStart_1322010 : Nat := 118140960795 + 1322010 * 2 ^ 59
def prefixEnd_1322010 : Nat := 4983230072969 + 3 ^ 40 * 1322010 * 2
def baseEnd_1322010 : Nat := 678826560050477863495193

theorem tailTrace_1322010 : CollatzResearch.WordTrace tailWord_1322010 prefixEnd_1322010 678826560050477863495193 := by
  unfold tailWord_1322010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054416485147756544434871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32145110627060684118492989 12054416485147756544434871)
  ·
    refine ⟨18081624727721634816652307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12054416485147756544434871 18081624727721634816652307)
    ·
      refine ⟨27122437091582452224978461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18081624727721634816652307 27122437091582452224978461)
      ·
        refine ⟨10170913909343419584366923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27122437091582452224978461 10170913909343419584366923)
        ·
          refine ⟨15256370864015129376550385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10170913909343419584366923 15256370864015129376550385)
          ·
            refine ⟨11442278148011347032412789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15256370864015129376550385 11442278148011347032412789)
            ·
              refine ⟨1072713576376063784288699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11442278148011347032412789 1072713576376063784288699)
              ·
                refine ⟨1609070364564095676433049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072713576376063784288699 1609070364564095676433049)
                ·
                  refine ⟨1206802773423071757324787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1609070364564095676433049 1206802773423071757324787)
                  ·
                    refine ⟨1810204160134607635987181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1206802773423071757324787 1810204160134607635987181)
                    ·
                      refine ⟨678826560050477863495193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810204160134607635987181 678826560050477863495193)
                      ·
                        rfl

theorem cell23_1322010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_1322010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322010 prefixEnd_1322010 := by exact prefixLift 1322010
  have htrace : WordTrace (prefixWord ++ tailWord_1322010) baseStart_1322010 baseEnd_1322010 := by
    simpa [prefixWord, tailWord_1322010, baseEnd_1322010] using wordTrace_append hprefix tailTrace_1322010
  have hstable : (prefixWord ++ tailWord_1322010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322010).length < 2 ^ (prefixWord ++ tailWord_1322010).sum := by decide
  have hdescent : baseEnd_1322010 < baseStart_1322010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322020 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1322020 : Nat := 118140960795 + 1322020 * 2 ^ 59
def prefixEnd_1322020 : Nat := 4983230072969 + 3 ^ 40 * 1322020 * 2
def baseEnd_1322020 : Nat := 678831694857022824370147

theorem tailTrace_1322020 : CollatzResearch.WordTrace tailWord_1322020 prefixEnd_1322020 678831694857022824370147 := by
  unfold tailWord_1322020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24109015335277398942801757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32145353780369865257069009 24109015335277398942801757)
  ·
    refine ⟨9040880750729024603550659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24109015335277398942801757 9040880750729024603550659)
    ·
      refine ⟨13561321126093536905325989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040880750729024603550659 13561321126093536905325989)
      ·
        refine ⟨2542747711142538169748623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13561321126093536905325989 2542747711142538169748623)
        ·
          refine ⟨3814121566713807254622935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542747711142538169748623 3814121566713807254622935)
          ·
            refine ⟨5721182350070710881934403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814121566713807254622935 5721182350070710881934403)
            ·
              refine ⟨8581773525106066322901605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721182350070710881934403 8581773525106066322901605)
              ·
                refine ⟨1609082535957387435544051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8581773525106066322901605 1609082535957387435544051)
                ·
                  refine ⟨2413623803936081153316077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609082535957387435544051 2413623803936081153316077)
                  ·
                    refine ⟨905108926476030432493529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413623803936081153316077 905108926476030432493529)
                    ·
                      refine ⟨678831694857022824370147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905108926476030432493529 678831694857022824370147)
                      ·
                        rfl

theorem cell23_1322020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1322020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322020 prefixEnd_1322020 := by exact prefixLift 1322020
  have htrace : WordTrace (prefixWord ++ tailWord_1322020) baseStart_1322020 baseEnd_1322020 := by
    simpa [prefixWord, tailWord_1322020, baseEnd_1322020] using wordTrace_append hprefix tailTrace_1322020
  have hstable : (prefixWord ++ tailWord_1322020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322020).length < 2 ^ (prefixWord ++ tailWord_1322020).sum := by decide
  have hdescent : baseEnd_1322020 < baseStart_1322020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322033 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 6, 2, 2]
def baseStart_1322033 : Nat := 118140960795 + 1322033 * 2 ^ 59
def prefixEnd_1322033 : Nat := 4983230072969 + 3 ^ 40 * 1322033 * 2
def baseEnd_1322033 : Nat := 678838370105531273507587

theorem tailTrace_1322033 : CollatzResearch.WordTrace tailWord_1322033 prefixEnd_1322033 678838370105531273507587 := by
  unfold tailWord_1322033
  simp only [CollatzResearch.WordTrace]
  refine ⟨48218504819507701105826753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32145669879671800737217835 48218504819507701105826753)
  ·
    refine ⟨36163878614630775829370065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48218504819507701105826753 36163878614630775829370065)
    ·
      refine ⟨27122908960973081872027549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36163878614630775829370065 27122908960973081872027549)
      ·
        refine ⟨10171090860364905702010331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27122908960973081872027549 10171090860364905702010331)
        ·
          refine ⟨15256636290547358553015497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10171090860364905702010331 15256636290547358553015497)
          ·
            refine ⟨11442477217910518914761623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15256636290547358553015497 11442477217910518914761623)
            ·
              refine ⟨17163715826865778372142435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11442477217910518914761623 17163715826865778372142435)
              ·
                refine ⟨25745573740298667558213653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17163715826865778372142435 25745573740298667558213653)
                ·
                  refine ⟨1206823769076500041791265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25745573740298667558213653 1206823769076500041791265)
                  ·
                    refine ⟨905117826807375031343449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1206823769076500041791265 905117826807375031343449)
                    ·
                      refine ⟨678838370105531273507587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905117826807375031343449 678838370105531273507587)
                      ·
                        rfl

theorem cell23_1322033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_1322033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322033 prefixEnd_1322033 := by exact prefixLift 1322033
  have htrace : WordTrace (prefixWord ++ tailWord_1322033) baseStart_1322033 baseEnd_1322033 := by
    simpa [prefixWord, tailWord_1322033, baseEnd_1322033] using wordTrace_append hprefix tailTrace_1322033
  have hstable : (prefixWord ++ tailWord_1322033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322033).length < 2 ^ (prefixWord ++ tailWord_1322033).sum := by decide
  have hdescent : baseEnd_1322033 < baseStart_1322033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322079 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1322079 : Nat := 118140960795 + 1322079 * 2 ^ 59
def prefixEnd_1322079 : Nat := 4983230072969 + 3 ^ 40 * 1322079 * 2
def baseEnd_1322079 : Nat := 678861990215638093532375

theorem tailTrace_1322079 : CollatzResearch.WordTrace tailWord_1322079 prefixEnd_1322079 678861990215638093532375 := by
  unfold tailWord_1322079
  simp only [CollatzResearch.WordTrace]
  refine ⟨48220182577341050962001291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32146788384894033974667527 48220182577341050962001291)
  ·
    refine ⟨72330273866011576443001937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48220182577341050962001291 72330273866011576443001937)
    ·
      refine ⟨54247705399508682332251453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72330273866011576443001937 54247705399508682332251453)
      ·
        refine ⟨20342889524815755874594295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54247705399508682332251453 20342889524815755874594295)
        ·
          refine ⟨30514334287223633811891443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20342889524815755874594295 30514334287223633811891443)
          ·
            refine ⟨45771501430835450717837165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30514334287223633811891443 45771501430835450717837165)
            ·
              refine ⟨17164313036563294019188937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45771501430835450717837165 17164313036563294019188937)
              ·
                refine ⟨12873234777422470514391703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17164313036563294019188937 12873234777422470514391703)
                ·
                  refine ⟨19309852166133705771587555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12873234777422470514391703 19309852166133705771587555)
                  ·
                    refine ⟨28964778249200558657381333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19309852166133705771587555 28964778249200558657381333)
                    ·
                      refine ⟨678861990215638093532375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28964778249200558657381333 678861990215638093532375)
                      ·
                        rfl

theorem cell23_1322079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1322079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322079 prefixEnd_1322079 := by exact prefixLift 1322079
  have htrace : WordTrace (prefixWord ++ tailWord_1322079) baseStart_1322079 baseEnd_1322079 := by
    simpa [prefixWord, tailWord_1322079, baseEnd_1322079] using wordTrace_append hprefix tailTrace_1322079
  have hstable : (prefixWord ++ tailWord_1322079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322079).length < 2 ^ (prefixWord ++ tailWord_1322079).sum := by decide
  have hdescent : baseEnd_1322079 < baseStart_1322079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322139 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_1322139 : Nat := 118140960795 + 1322139 * 2 ^ 59
def prefixEnd_1322139 : Nat := 4983230072969 + 3 ^ 40 * 1322139 * 2
def baseEnd_1322139 : Nat := 678892799054907858782099

theorem tailTrace_1322139 : CollatzResearch.WordTrace tailWord_1322139 prefixEnd_1322139 678892799054907858782099 := by
  unfold tailWord_1322139
  simp only [CollatzResearch.WordTrace]
  refine ⟨48222370957123681209185471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32148247304749120806123647 48222370957123681209185471)
  ·
    refine ⟨72333556435685521813778207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48222370957123681209185471 72333556435685521813778207)
    ·
      refine ⟨108500334653528282720667311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72333556435685521813778207 108500334653528282720667311)
      ·
        refine ⟨162750501980292424081000967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108500334653528282720667311 162750501980292424081000967)
        ·
          refine ⟨244125752970438636121501451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162750501980292424081000967 244125752970438636121501451)
          ·
            refine ⟨366188629455657954182252177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244125752970438636121501451 366188629455657954182252177)
            ·
              refine ⟨274641472091743465636689133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366188629455657954182252177 274641472091743465636689133)
              ·
                refine ⟨102990552034403799613758425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274641472091743465636689133 102990552034403799613758425)
                ·
                  refine ⟨77242914025802849710318819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102990552034403799613758425 77242914025802849710318819)
                  ·
                    refine ⟨115864371038704274565478229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77242914025802849710318819 115864371038704274565478229)
                    ·
                      refine ⟨678892799054907858782099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 115864371038704274565478229 678892799054907858782099)
                      ·
                        rfl

theorem cell23_1322139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_1322139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322139 prefixEnd_1322139 := by exact prefixLift 1322139
  have htrace : WordTrace (prefixWord ++ tailWord_1322139) baseStart_1322139 baseEnd_1322139 := by
    simpa [prefixWord, tailWord_1322139, baseEnd_1322139] using wordTrace_append hprefix tailTrace_1322139
  have hstable : (prefixWord ++ tailWord_1322139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322139).length < 2 ^ (prefixWord ++ tailWord_1322139).sum := by decide
  have hdescent : baseEnd_1322139 < baseStart_1322139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322140 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1322140 : Nat := 118140960795 + 1322140 * 2 ^ 59
def prefixEnd_1322140 : Nat := 4983230072969 + 3 ^ 40 * 1322140 * 2
def baseEnd_1322140 : Nat := 678893312535562354869595

theorem tailTrace_1322140 : CollatzResearch.WordTrace tailWord_1322140 prefixEnd_1322140 678893312535562354869595 := by
  unfold tailWord_1322140
  simp only [CollatzResearch.WordTrace]
  refine ⟨24111203715060029189985937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32148271620080038919981249 24111203715060029189985937)
  ·
    refine ⟨18083402786295021892489453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24111203715060029189985937 18083402786295021892489453)
    ·
      refine ⟨6781276044860633209683545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18083402786295021892489453 6781276044860633209683545)
      ·
        refine ⟨5085957033645474907262659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6781276044860633209683545 5085957033645474907262659)
        ·
          refine ⟨7628935550468212360893989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5085957033645474907262659 7628935550468212360893989)
          ·
            refine ⟨1430425415712789817667623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7628935550468212360893989 1430425415712789817667623)
            ·
              refine ⟨2145638123569184726501435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430425415712789817667623 2145638123569184726501435)
              ·
                refine ⟨3218457185353777089752153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145638123569184726501435 3218457185353777089752153)
                ·
                  refine ⟨2413842889015332817314115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3218457185353777089752153 2413842889015332817314115)
                  ·
                    refine ⟨3620764333522999225971173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2413842889015332817314115 3620764333522999225971173)
                    ·
                      refine ⟨678893312535562354869595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3620764333522999225971173 678893312535562354869595)
                      ·
                        rfl

theorem cell23_1322140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1322140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322140 prefixEnd_1322140 := by exact prefixLift 1322140
  have htrace : WordTrace (prefixWord ++ tailWord_1322140) baseStart_1322140 baseEnd_1322140 := by
    simpa [prefixWord, tailWord_1322140, baseEnd_1322140] using wordTrace_append hprefix tailTrace_1322140
  have hstable : (prefixWord ++ tailWord_1322140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322140).length < 2 ^ (prefixWord ++ tailWord_1322140).sum := by decide
  have hdescent : baseEnd_1322140 < baseStart_1322140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322207 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 1, 1, 3]
def baseStart_1322207 : Nat := 118140960795 + 1322207 * 2 ^ 59
def prefixEnd_1322207 : Nat := 4983230072969 + 3 ^ 40 * 1322207 * 2
def baseEnd_1322207 : Nat := 678927715739413592731787

theorem tailTrace_1322207 : CollatzResearch.WordTrace tailWord_1322207 prefixEnd_1322207 678927715739413592731787 := by
  unfold tailWord_1322207
  simp only [CollatzResearch.WordTrace]
  refine ⟨48224851120877328822660875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32149900747251552548440583 48224851120877328822660875)
  ·
    refine ⟨72337276681315993233991313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48224851120877328822660875 72337276681315993233991313)
    ·
      refine ⟨54252957510986994925493485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72337276681315993233991313 54252957510986994925493485)
      ·
        refine ⟨20344859066620123097060057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54252957510986994925493485 20344859066620123097060057)
        ·
          refine ⟨15258644299965092322795043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20344859066620123097060057 15258644299965092322795043)
          ·
            refine ⟨22887966449947638484192565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15258644299965092322795043 22887966449947638484192565)
            ·
              refine ⟨2145746854682591107893053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22887966449947638484192565 2145746854682591107893053)
              ·
                refine ⟨804655070505971665459895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2145746854682591107893053 804655070505971665459895)
                ·
                  refine ⟨1206982605758957498189843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804655070505971665459895 1206982605758957498189843)
                  ·
                    refine ⟨1810473908638436247284765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1206982605758957498189843 1810473908638436247284765)
                    ·
                      refine ⟨678927715739413592731787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810473908638436247284765 678927715739413592731787)
                      ·
                        rfl

theorem cell23_1322207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_1322207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322207 prefixEnd_1322207 := by exact prefixLift 1322207
  have htrace : WordTrace (prefixWord ++ tailWord_1322207) baseStart_1322207 baseEnd_1322207 := by
    simpa [prefixWord, tailWord_1322207, baseEnd_1322207] using wordTrace_append hprefix tailTrace_1322207
  have hstable : (prefixWord ++ tailWord_1322207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322207).length < 2 ^ (prefixWord ++ tailWord_1322207).sum := by decide
  have hdescent : baseEnd_1322207 < baseStart_1322207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322233 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_1322233 : Nat := 118140960795 + 1322233 * 2 ^ 59
def prefixEnd_1322233 : Nat := 4983230072969 + 3 ^ 40 * 1322233 * 2
def baseEnd_1322233 : Nat := 678941066236430491006667

theorem tailTrace_1322233 : CollatzResearch.WordTrace tailWord_1322233 prefixEnd_1322233 678941066236430491006667 := by
  unfold tailWord_1322233
  simp only [CollatzResearch.WordTrace]
  refine ⟨48225799418783135263107353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32150532945855423508738235 48225799418783135263107353)
  ·
    refine ⟨36169349564087351447330515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48225799418783135263107353 36169349564087351447330515)
    ·
      refine ⟨54254024346131027170995773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36169349564087351447330515 54254024346131027170995773)
      ·
        refine ⟨20345259129799135189123415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54254024346131027170995773 20345259129799135189123415)
        ·
          refine ⟨30517888694698702783685123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20345259129799135189123415 30517888694698702783685123)
          ·
            refine ⟨45776833042048054175527685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30517888694698702783685123 45776833042048054175527685)
            ·
              refine ⟨8583156195384010157911441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45776833042048054175527685 8583156195384010157911441)
              ·
                refine ⟨6437367146538007618433581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8583156195384010157911441 6437367146538007618433581)
                ·
                  refine ⟨2414012679951752856912593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6437367146538007618433581 2414012679951752856912593)
                  ·
                    refine ⟨1810509509963814642684445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414012679951752856912593 1810509509963814642684445)
                    ·
                      refine ⟨678941066236430491006667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810509509963814642684445 678941066236430491006667)
                      ·
                        rfl

theorem cell23_1322233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_1322233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322233 prefixEnd_1322233 := by exact prefixLift 1322233
  have htrace : WordTrace (prefixWord ++ tailWord_1322233) baseStart_1322233 baseEnd_1322233 := by
    simpa [prefixWord, tailWord_1322233, baseEnd_1322233] using wordTrace_append hprefix tailTrace_1322233
  have hstable : (prefixWord ++ tailWord_1322233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322233).length < 2 ^ (prefixWord ++ tailWord_1322233).sum := by decide
  have hdescent : baseEnd_1322233 < baseStart_1322233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322270 : List Nat := [4, 3, 2, 1, 2, 11]
def baseStart_1322270 : Nat := 118140960795 + 1322270 * 2 ^ 59
def prefixEnd_1322270 : Nat := 4983230072969 + 3 ^ 40 * 1322270 * 2
def baseEnd_1322270 : Nat := 2794074341648752453679

theorem tailTrace_1322270 : CollatzResearch.WordTrace tailWord_1322270 prefixEnd_1322270 2794074341648752453679 := by
  unfold tailWord_1322270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028393614956136322775533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32151432613099393721469509 6028393614956136322775533)
  ·
    refine ⟨2260647605608551121040825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6028393614956136322775533 2260647605608551121040825)
    ·
      refine ⟨1695485704206413340780619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2260647605608551121040825 1695485704206413340780619)
      ·
        refine ⟨2543228556309620011170929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695485704206413340780619 2543228556309620011170929)
        ·
          refine ⟨1907421417232215008378197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2543228556309620011170929 1907421417232215008378197)
          ·
            refine ⟨2794074341648752453679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1907421417232215008378197 2794074341648752453679)
            ·
              rfl

theorem cell23_1322270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 11].length) (baseStart_1322270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322270 prefixEnd_1322270 := by exact prefixLift 1322270
  have htrace : WordTrace (prefixWord ++ tailWord_1322270) baseStart_1322270 baseEnd_1322270 := by
    simpa [prefixWord, tailWord_1322270, baseEnd_1322270] using wordTrace_append hprefix tailTrace_1322270
  have hstable : (prefixWord ++ tailWord_1322270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322270).length < 2 ^ (prefixWord ++ tailWord_1322270).sum := by decide
  have hdescent : baseEnd_1322270 < baseStart_1322270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322294 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1322294 : Nat := 118140960795 + 1322294 * 2 ^ 59
def prefixEnd_1322294 : Nat := 4983230072969 + 3 ^ 40 * 1322294 * 2
def baseEnd_1322294 : Nat := 678972388556354752343887

theorem tailTrace_1322294 : CollatzResearch.WordTrace tailWord_1322294 prefixEnd_1322294 678972388556354752343887 := by
  unfold tailWord_1322294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014251516972633917567371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32152016181041428454051957 3014251516972633917567371)
  ·
    refine ⟨4521377275458950876351057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3014251516972633917567371 4521377275458950876351057)
    ·
      refine ⟨3391032956594213157263293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4521377275458950876351057 3391032956594213157263293)
      ·
        refine ⟨1271637358722829933973735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3391032956594213157263293 1271637358722829933973735)
        ·
          refine ⟨1907456038084244900960603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271637358722829933973735 1907456038084244900960603)
          ·
            refine ⟨2861184057126367351440905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907456038084244900960603 2861184057126367351440905)
            ·
              refine ⟨2145888042844775513580679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861184057126367351440905 2145888042844775513580679)
              ·
                refine ⟨3218832064267163270371019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145888042844775513580679 3218832064267163270371019)
                ·
                  refine ⟨4828248096400744905556529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218832064267163270371019 4828248096400744905556529)
                  ·
                    refine ⟨3621186072300558679167397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828248096400744905556529 3621186072300558679167397)
                    ·
                      refine ⟨678972388556354752343887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3621186072300558679167397 678972388556354752343887)
                      ·
                        rfl

theorem cell23_1322294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1322294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322294 prefixEnd_1322294 := by exact prefixLift 1322294
  have htrace : WordTrace (prefixWord ++ tailWord_1322294) baseStart_1322294 baseEnd_1322294 := by
    simpa [prefixWord, tailWord_1322294, baseEnd_1322294] using wordTrace_append hprefix tailTrace_1322294
  have hstable : (prefixWord ++ tailWord_1322294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322294).length < 2 ^ (prefixWord ++ tailWord_1322294).sum := by decide
  have hdescent : baseEnd_1322294 < baseStart_1322294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322297 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1322297 : Nat := 118140960795 + 1322297 * 2 ^ 59
def prefixEnd_1322297 : Nat := 4983230072969 + 3 ^ 40 * 1322297 * 2
def baseEnd_1322297 : Nat := 678973928998318240606373

theorem tailTrace_1322297 : CollatzResearch.WordTrace tailWord_1322297 prefixEnd_1322297 678973928998318240606373 := by
  unfold tailWord_1322297
  simp only [CollatzResearch.WordTrace]
  refine ⟨48228133690551274193437145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32152089127034182795624763 48228133690551274193437145)
  ·
    refine ⟨36171100267913455645077859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48228133690551274193437145 36171100267913455645077859)
    ·
      refine ⟨54256650401870183467616789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36171100267913455645077859 54256650401870183467616789)
      ·
        refine ⟨2543280487587664850044537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54256650401870183467616789 2543280487587664850044537)
        ·
          refine ⟨1907460365690748637533403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2543280487587664850044537 1907460365690748637533403)
          ·
            refine ⟨2861190548536122956300105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907460365690748637533403 2861190548536122956300105)
            ·
              refine ⟨2145892911402092217225079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861190548536122956300105 2145892911402092217225079)
              ·
                refine ⟨3218839367103138325837619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145892911402092217225079 3218839367103138325837619)
                ·
                  refine ⟨4828259050654707488756429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218839367103138325837619 4828259050654707488756429)
                  ·
                    refine ⟨1810597143995515308283661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4828259050654707488756429 1810597143995515308283661)
                    ·
                      refine ⟨678973928998318240606373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1810597143995515308283661 678973928998318240606373)
                      ·
                        rfl

theorem cell23_1322297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1322297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322297 prefixEnd_1322297 := by exact prefixLift 1322297
  have htrace : WordTrace (prefixWord ++ tailWord_1322297) baseStart_1322297 baseEnd_1322297 := by
    simpa [prefixWord, tailWord_1322297, baseEnd_1322297] using wordTrace_append hprefix tailTrace_1322297
  have hstable : (prefixWord ++ tailWord_1322297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322297).length < 2 ^ (prefixWord ++ tailWord_1322297).sum := by decide
  have hdescent : baseEnd_1322297 < baseStart_1322297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322320 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 1, 4, 2]
def baseStart_1322320 : Nat := 118140960795 + 1322320 * 2 ^ 59
def prefixEnd_1322320 : Nat := 4983230072969 + 3 ^ 40 * 1322320 * 2
def baseEnd_1322320 : Nat := 678985739053371650618767

theorem tailTrace_1322320 : CollatzResearch.WordTrace tailWord_1322320 prefixEnd_1322320 678985739053371650618767 := by
  unfold tailWord_1322320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24114486284733974560762207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32152648379645299414349609 24114486284733974560762207)
  ·
    refine ⟨36171729427100961841143311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24114486284733974560762207 36171729427100961841143311)
    ·
      refine ⟨54257594140651442761714967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36171729427100961841143311 54257594140651442761714967)
      ·
        refine ⟨81386391210977164142572451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54257594140651442761714967 81386391210977164142572451)
        ·
          refine ⟨122079586816465746213858677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81386391210977164142572451 122079586816465746213858677)
          ·
            refine ⟨11444961264043663707549251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122079586816465746213858677 11444961264043663707549251)
            ·
              refine ⟨17167441896065495561323877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11444961264043663707549251 17167441896065495561323877)
              ·
                refine ⟨3218895355512280417748227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17167441896065495561323877 3218895355512280417748227)
                ·
                  refine ⟨4828343033268420626622341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218895355512280417748227 4828343033268420626622341)
                  ·
                    refine ⟨905314318737828867491689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828343033268420626622341 905314318737828867491689)
                    ·
                      refine ⟨678985739053371650618767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905314318737828867491689 678985739053371650618767)
                      ·
                        rfl

theorem cell23_1322320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 4, 2].length) (baseStart_1322320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322320 prefixEnd_1322320 := by exact prefixLift 1322320
  have htrace : WordTrace (prefixWord ++ tailWord_1322320) baseStart_1322320 baseEnd_1322320 := by
    simpa [prefixWord, tailWord_1322320, baseEnd_1322320] using wordTrace_append hprefix tailTrace_1322320
  have hstable : (prefixWord ++ tailWord_1322320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322320).length < 2 ^ (prefixWord ++ tailWord_1322320).sum := by decide
  have hdescent : baseEnd_1322320 < baseStart_1322320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322373 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_1322373 : Nat := 118140960795 + 1322373 * 2 ^ 59
def prefixEnd_1322373 : Nat := 4983230072969 + 3 ^ 40 * 1322373 * 2
def baseEnd_1322373 : Nat := 226337651176019981085341

theorem tailTrace_1322373 : CollatzResearch.WordTrace tailWord_1322373 prefixEnd_1322373 226337651176019981085341 := by
  unfold tailWord_1322373
  simp only [CollatzResearch.WordTrace]
  refine ⟨48230905638275939173203773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32153937092183959448802515 48230905638275939173203773)
  ·
    refine ⟨18086589614353477189951415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48230905638275939173203773 18086589614353477189951415)
    ·
      refine ⟨27129884421530215784927123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18086589614353477189951415 27129884421530215784927123)
      ·
        refine ⟨40694826632295323677390685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27129884421530215784927123 40694826632295323677390685)
        ·
          refine ⟨15260559987110746379021507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40694826632295323677390685 15260559987110746379021507)
          ·
            refine ⟨22890839980666119568532261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15260559987110746379021507 22890839980666119568532261)
            ·
              refine ⟨4292032496374897419099799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22890839980666119568532261 4292032496374897419099799)
              ·
                refine ⟨6438048744562346128649699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292032496374897419099799 6438048744562346128649699)
                ·
                  refine ⟨9657073116843519192974549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6438048744562346128649699 9657073116843519192974549)
                  ·
                    refine ⟨226337651176019981085341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9657073116843519192974549 226337651176019981085341)
                    ·
                      rfl

theorem cell23_1322373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_1322373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322373 prefixEnd_1322373 := by exact prefixLift 1322373
  have htrace : WordTrace (prefixWord ++ tailWord_1322373) baseStart_1322373 baseEnd_1322373 := by
    simpa [prefixWord, tailWord_1322373, baseEnd_1322373] using wordTrace_append hprefix tailTrace_1322373
  have hstable : (prefixWord ++ tailWord_1322373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322373).length < 2 ^ (prefixWord ++ tailWord_1322373).sum := by decide
  have hdescent : baseEnd_1322373 < baseStart_1322373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322473 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_1322473 : Nat := 118140960795 + 1322473 * 2 ^ 59
def prefixEnd_1322473 : Nat := 4983230072969 + 3 ^ 40 * 1322473 * 2
def baseEnd_1322473 : Nat := 679064301593509552005563

theorem tailTrace_1322473 : CollatzResearch.WordTrace tailWord_1322473 prefixEnd_1322473 679064301593509552005563 := by
  unfold tailWord_1322473
  simp only [CollatzResearch.WordTrace]
  refine ⟨48234552937913656251844073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32156368625275770834562715 48234552937913656251844073)
  ·
    refine ⟨36175914703435242188883055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48234552937913656251844073 36175914703435242188883055)
    ·
      refine ⟨54263872055152863283324583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36175914703435242188883055 54263872055152863283324583)
      ·
        refine ⟨81395808082729294924986875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54263872055152863283324583 81395808082729294924986875)
        ·
          refine ⟨122093712124093942387480313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81395808082729294924986875 122093712124093942387480313)
          ·
            refine ⟨91570284093070456790610235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122093712124093942387480313 91570284093070456790610235)
            ·
              refine ⟨137355426139605685185915353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91570284093070456790610235 137355426139605685185915353)
              ·
                refine ⟨103016569604704263889436515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137355426139605685185915353 103016569604704263889436515)
                ·
                  refine ⟨154524854407056395834154773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103016569604704263889436515 154524854407056395834154773)
                  ·
                    refine ⟨7243352550330768554726005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 154524854407056395834154773 7243352550330768554726005)
                    ·
                      refine ⟨679064301593509552005563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7243352550330768554726005 679064301593509552005563)
                      ·
                        rfl

theorem cell23_1322473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_1322473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322473 prefixEnd_1322473 := by exact prefixLift 1322473
  have htrace : WordTrace (prefixWord ++ tailWord_1322473) baseStart_1322473 baseEnd_1322473 := by
    simpa [prefixWord, tailWord_1322473, baseEnd_1322473] using wordTrace_append hprefix tailTrace_1322473
  have hstable : (prefixWord ++ tailWord_1322473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322473).length < 2 ^ (prefixWord ++ tailWord_1322473).sum := by decide
  have hdescent : baseEnd_1322473 < baseStart_1322473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322480 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_1322480 : Nat := 118140960795 + 1322480 * 2 ^ 59
def prefixEnd_1322480 : Nat := 4983230072969 + 3 ^ 40 * 1322480 * 2
def baseEnd_1322480 : Nat := 226355965319363674872677

theorem tailTrace_1322480 : CollatzResearch.WordTrace tailWord_1322480 prefixEnd_1322480 226355965319363674872677 := by
  unfold tailWord_1322480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24117404124444148223674447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32156538832592197631565929 24117404124444148223674447)
  ·
    refine ⟨36176106186666222335511671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24117404124444148223674447 36176106186666222335511671)
    ·
      refine ⟨54264159279999333503267507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36176106186666222335511671 54264159279999333503267507)
      ·
        refine ⟨81396238919999000254901261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54264159279999333503267507 81396238919999000254901261)
        ·
          refine ⟨30523589594999625095587973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81396238919999000254901261 30523589594999625095587973)
          ·
            refine ⟨5723173049062429705422745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30523589594999625095587973 5723173049062429705422745)
            ·
              refine ⟨4292379786796822279067059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5723173049062429705422745 4292379786796822279067059)
              ·
                refine ⟨6438569680195233418600589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292379786796822279067059 6438569680195233418600589)
                ·
                  refine ⟨2414463630073212531975221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438569680195233418600589 2414463630073212531975221)
                  ·
                    refine ⟨226355965319363674872677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2414463630073212531975221 226355965319363674872677)
                    ·
                      rfl

theorem cell23_1322480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_1322480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322480 prefixEnd_1322480 := by exact prefixLift 1322480
  have htrace : WordTrace (prefixWord ++ tailWord_1322480) baseStart_1322480 baseEnd_1322480 := by
    simpa [prefixWord, tailWord_1322480, baseEnd_1322480] using wordTrace_append hprefix tailTrace_1322480
  have hstable : (prefixWord ++ tailWord_1322480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322480).length < 2 ^ (prefixWord ++ tailWord_1322480).sum := by decide
  have hdescent : baseEnd_1322480 < baseStart_1322480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322487 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 2, 3, 2]
def baseStart_1322487 : Nat := 118140960795 + 1322487 * 2 ^ 59
def prefixEnd_1322487 : Nat := 4983230072969 + 3 ^ 40 * 1322487 * 2
def baseEnd_1322487 : Nat := 679071490322672497230499

theorem tailTrace_1322487 : CollatzResearch.WordTrace tailWord_1322487 prefixEnd_1322487 679071490322672497230499 := by
  unfold tailWord_1322487
  simp only [CollatzResearch.WordTrace]
  refine ⟨48235063559862936642853715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32156709039908624428569143 48235063559862936642853715)
  ·
    refine ⟨72352595339794404964280573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48235063559862936642853715 72352595339794404964280573)
    ·
      refine ⟨27132223252422901861605215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72352595339794404964280573 27132223252422901861605215)
      ·
        refine ⟨40698334878634352792407823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27132223252422901861605215 40698334878634352792407823)
        ·
          refine ⟨61047502317951529188611735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40698334878634352792407823 61047502317951529188611735)
          ·
            refine ⟨91571253476927293782917603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61047502317951529188611735 91571253476927293782917603)
            ·
              refine ⟨137356880215390940674376405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91571253476927293782917603 137356880215390940674376405)
              ·
                refine ⟨3219301880048225172055697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137356880215390940674376405 3219301880048225172055697)
                ·
                  refine ⟨2414476410036168879041773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3219301880048225172055697 2414476410036168879041773)
                  ·
                    refine ⟨905428653763563329640665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414476410036168879041773 905428653763563329640665)
                    ·
                      refine ⟨679071490322672497230499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905428653763563329640665 679071490322672497230499)
                      ·
                        rfl

theorem cell23_1322487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_1322487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322487 prefixEnd_1322487 := by exact prefixLift 1322487
  have htrace : WordTrace (prefixWord ++ tailWord_1322487) baseStart_1322487 baseEnd_1322487 := by
    simpa [prefixWord, tailWord_1322487, baseEnd_1322487] using wordTrace_append hprefix tailTrace_1322487
  have hstable : (prefixWord ++ tailWord_1322487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322487).length < 2 ^ (prefixWord ++ tailWord_1322487).sum := by decide
  have hdescent : baseEnd_1322487 < baseStart_1322487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322527 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 2, 4]
def baseStart_1322527 : Nat := 118140960795 + 1322527 * 2 ^ 59
def prefixEnd_1322527 : Nat := 4983230072969 + 3 ^ 40 * 1322527 * 2
def baseEnd_1322527 : Nat := 226364009849617446910105

theorem tailTrace_1322527 : CollatzResearch.WordTrace tailWord_1322527 prefixEnd_1322527 226364009849617446910105 := by
  unfold tailWord_1322527
  simp only [CollatzResearch.WordTrace]
  refine ⟨48236522479718023474309835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32157681653145348982873223 48236522479718023474309835)
  ·
    refine ⟨72354783719577035211464753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48236522479718023474309835 72354783719577035211464753)
    ·
      refine ⟨54266087789682776408598565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72354783719577035211464753 54266087789682776408598565)
      ·
        refine ⟨10174891460565520576612231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54266087789682776408598565 10174891460565520576612231)
        ·
          refine ⟨15262337190848280864918347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10174891460565520576612231 15262337190848280864918347)
          ·
            refine ⟨22893505786272421297377521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15262337190848280864918347 22893505786272421297377521)
            ·
              refine ⟨17170129339704315973033141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22893505786272421297377521 17170129339704315973033141)
              ·
                refine ⟨1609699625597279622471857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17170129339704315973033141 1609699625597279622471857)
                ·
                  refine ⟨1207274719197959716853893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1609699625597279622471857 1207274719197959716853893)
                  ·
                    refine ⟨226364009849617446910105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207274719197959716853893 226364009849617446910105)
                    ·
                      rfl

theorem cell23_1322527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_1322527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322527 prefixEnd_1322527 := by exact prefixLift 1322527
  have htrace : WordTrace (prefixWord ++ tailWord_1322527) baseStart_1322527 baseEnd_1322527 := by
    simpa [prefixWord, tailWord_1322527, baseEnd_1322527] using wordTrace_append hprefix tailTrace_1322527
  have hstable : (prefixWord ++ tailWord_1322527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322527).length < 2 ^ (prefixWord ++ tailWord_1322527).sum := by decide
  have hdescent : baseEnd_1322527 < baseStart_1322527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322557 : List Nat := [1, 4, 1, 3, 3, 2, 9]
def baseStart_1322557 : Nat := 118140960795 + 1322557 * 2 ^ 59
def prefixEnd_1322557 : Nat := 4983230072969 + 3 ^ 40 * 1322557 * 2
def baseEnd_1322557 : Nat := 8384042394672681769817

theorem tailTrace_1322557 : CollatzResearch.WordTrace tailWord_1322557 prefixEnd_1322557 8384042394672681769817 := by
  unfold tailWord_1322557
  simp only [CollatzResearch.WordTrace]
  refine ⟨48237616669609338597901925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32158411113072892398601283 48237616669609338597901925)
  ·
    refine ⟨9044553125551750987106611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48237616669609338597901925 9044553125551750987106611)
    ·
      refine ⟨13566829688327626480659917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9044553125551750987106611 13566829688327626480659917)
      ·
        refine ⟨5087561133122859930247469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13566829688327626480659917 5087561133122859930247469)
        ·
          refine ⟨1907835424921072473842801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5087561133122859930247469 1907835424921072473842801)
          ·
            refine ⟨1430876568690804355382101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1907835424921072473842801 1430876568690804355382101)
            ·
              refine ⟨8384042394672681769817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1430876568690804355382101 8384042394672681769817)
              ·
                rfl

theorem cell23_1322557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 9].length) (baseStart_1322557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322557 prefixEnd_1322557 := by exact prefixLift 1322557
  have htrace : WordTrace (prefixWord ++ tailWord_1322557) baseStart_1322557 baseEnd_1322557 := by
    simpa [prefixWord, tailWord_1322557, baseEnd_1322557] using wordTrace_append hprefix tailTrace_1322557
  have hstable : (prefixWord ++ tailWord_1322557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322557).length < 2 ^ (prefixWord ++ tailWord_1322557).sum := by decide
  have hdescent : baseEnd_1322557 < baseStart_1322557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322570 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1322570 : Nat := 118140960795 + 1322570 * 2 ^ 59
def prefixEnd_1322570 : Nat := 4983230072969 + 3 ^ 40 * 1322570 * 2
def baseEnd_1322570 : Nat := 226371369738998557497539

theorem tailTrace_1322570 : CollatzResearch.WordTrace tailWord_1322570 prefixEnd_1322570 226371369738998557497539 := by
  unfold tailWord_1322570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12059522704640560454531291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32158727212374827878750109 12059522704640560454531291)
  ·
    refine ⟨18089284056960840681796937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12059522704640560454531291 18089284056960840681796937)
    ·
      refine ⟨13566963042720630511347703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18089284056960840681796937 13566963042720630511347703)
      ·
        refine ⟨20350444564080945767021555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13566963042720630511347703 20350444564080945767021555)
        ·
          refine ⟨30525666846121418650532333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20350444564080945767021555 30525666846121418650532333)
          ·
            refine ⟨11447125067295531993949625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30525666846121418650532333 11447125067295531993949625)
            ·
              refine ⟨8585343800471648995462219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11447125067295531993949625 8585343800471648995462219)
              ·
                refine ⟨12878015700707473493193329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8585343800471648995462219 12878015700707473493193329)
                ·
                  refine ⟨9658511775530605119894997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12878015700707473493193329 9658511775530605119894997)
                  ·
                    refine ⟨226371369738998557497539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9658511775530605119894997 226371369738998557497539)
                    ·
                      rfl

theorem cell23_1322570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1322570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322570 prefixEnd_1322570 := by exact prefixLift 1322570
  have htrace : WordTrace (prefixWord ++ tailWord_1322570) baseStart_1322570 baseEnd_1322570 := by
    simpa [prefixWord, tailWord_1322570, baseEnd_1322570] using wordTrace_append hprefix tailTrace_1322570
  have hstable : (prefixWord ++ tailWord_1322570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322570).length < 2 ^ (prefixWord ++ tailWord_1322570).sum := by decide
  have hdescent : baseEnd_1322570 < baseStart_1322570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322620 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1322620 : Nat := 118140960795 + 1322620 * 2 ^ 59
def prefixEnd_1322620 : Nat := 4983230072969 + 3 ^ 40 * 1322620 * 2
def baseEnd_1322620 : Nat := 679139783249720476867387

theorem tailTrace_1322620 : CollatzResearch.WordTrace tailWord_1322620 prefixEnd_1322620 679139783249720476867387 := by
  unfold tailWord_1322620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24119957234190550178722657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32159942978920733571630209 24119957234190550178722657)
  ·
    refine ⟨18089967925642912634041993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24119957234190550178722657 18089967925642912634041993)
    ·
      refine ⟨13567475944232184475531495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18089967925642912634041993 13567475944232184475531495)
      ·
        refine ⟨20351213916348276713297243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13567475944232184475531495 20351213916348276713297243)
        ·
          refine ⟨30526820874522415069945865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20351213916348276713297243 30526820874522415069945865)
          ·
            refine ⟨22895115655891811302459399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30526820874522415069945865 22895115655891811302459399)
            ·
              refine ⟨34342673483837716953689099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22895115655891811302459399 34342673483837716953689099)
              ·
                refine ⟨51514010225756575430533649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34342673483837716953689099 51514010225756575430533649)
                ·
                  refine ⟨38635507669317431572900237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51514010225756575430533649 38635507669317431572900237)
                  ·
                    refine ⟨14488315375994036839837589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38635507669317431572900237 14488315375994036839837589)
                    ·
                      refine ⟨679139783249720476867387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14488315375994036839837589 679139783249720476867387)
                      ·
                        rfl

theorem cell23_1322620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1322620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322620 prefixEnd_1322620 := by exact prefixLift 1322620
  have htrace : WordTrace (prefixWord ++ tailWord_1322620) baseStart_1322620 baseEnd_1322620 := by
    simpa [prefixWord, tailWord_1322620, baseEnd_1322620] using wordTrace_append hprefix tailTrace_1322620
  have hstable : (prefixWord ++ tailWord_1322620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322620).length < 2 ^ (prefixWord ++ tailWord_1322620).sum := by decide
  have hdescent : baseEnd_1322620 < baseStart_1322620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322647 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 7]
def baseStart_1322647 : Nat := 118140960795 + 1322647 * 2 ^ 59
def prefixEnd_1322647 : Nat := 4983230072969 + 3 ^ 40 * 1322647 * 2
def baseEnd_1322647 : Nat := 75461516358599096803307

theorem tailTrace_1322647 : CollatzResearch.WordTrace tailWord_1322647 prefixEnd_1322647 75461516358599096803307 := by
  unfold tailWord_1322647
  simp only [CollatzResearch.WordTrace]
  refine ⟨48240899239283283968678195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32160599492855522645785463 48240899239283283968678195)
  ·
    refine ⟨72361348858924925953017293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48240899239283283968678195 72361348858924925953017293)
    ·
      refine ⟨27135505822096847232381485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72361348858924925953017293 27135505822096847232381485)
      ·
        refine ⟨10175814683286317712143057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27135505822096847232381485 10175814683286317712143057)
        ·
          refine ⟨7631861012464738284107293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10175814683286317712143057 7631861012464738284107293)
          ·
            refine ⟨2861947879674276856540235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7631861012464738284107293 2861947879674276856540235)
            ·
              refine ⟨4292921819511415284810353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861947879674276856540235 4292921819511415284810353)
              ·
                refine ⟨3219691364633561463607765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4292921819511415284810353 3219691364633561463607765)
                ·
                  refine ⟨75461516358599096803307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3219691364633561463607765 75461516358599096803307)
                  ·
                    rfl

theorem cell23_1322647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 7].length) (baseStart_1322647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322647 prefixEnd_1322647 := by exact prefixLift 1322647
  have htrace : WordTrace (prefixWord ++ tailWord_1322647) baseStart_1322647 baseEnd_1322647 := by
    simpa [prefixWord, tailWord_1322647, baseEnd_1322647] using wordTrace_append hprefix tailTrace_1322647
  have hstable : (prefixWord ++ tailWord_1322647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322647).length < 2 ^ (prefixWord ++ tailWord_1322647).sum := by decide
  have hdescent : baseEnd_1322647 < baseStart_1322647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322707 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 9, 4]
def baseStart_1322707 : Nat := 118140960795 + 1322707 * 2 ^ 59
def prefixEnd_1322707 : Nat := 4983230072969 + 3 ^ 40 * 1322707 * 2
def baseEnd_1322707 : Nat := 226394818688887212159829

theorem tailTrace_1322707 : CollatzResearch.WordTrace tailWord_1322707 prefixEnd_1322707 226394818688887212159829 := by
  unfold tailWord_1322707
  simp only [CollatzResearch.WordTrace]
  refine ⟨48243087619065914215862375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32162058412710609477241583 48243087619065914215862375)
  ·
    refine ⟨72364631428598871323793563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48243087619065914215862375 72364631428598871323793563)
    ·
      refine ⟨108546947142898306985690345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72364631428598871323793563 108546947142898306985690345)
      ·
        refine ⟨81410210357173730239267759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108546947142898306985690345 81410210357173730239267759)
        ·
          refine ⟨122115315535760595358901639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81410210357173730239267759 122115315535760595358901639)
          ·
            refine ⟨183172973303640893038352459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122115315535760595358901639 183172973303640893038352459)
            ·
              refine ⟨274759459955461339557528689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183172973303640893038352459 274759459955461339557528689)
              ·
                refine ⟨206069594966596004668146517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274759459955461339557528689 206069594966596004668146517)
                ·
                  refine ⟨1207439033007398464852421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 206069594966596004668146517 1207439033007398464852421)
                  ·
                    refine ⟨226394818688887212159829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207439033007398464852421 226394818688887212159829)
                    ·
                      rfl

theorem cell23_1322707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 4].length) (baseStart_1322707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322707 prefixEnd_1322707 := by exact prefixLift 1322707
  have htrace : WordTrace (prefixWord ++ tailWord_1322707) baseStart_1322707 baseEnd_1322707 := by
    simpa [prefixWord, tailWord_1322707, baseEnd_1322707] using wordTrace_append hprefix tailTrace_1322707
  have hstable : (prefixWord ++ tailWord_1322707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322707).length < 2 ^ (prefixWord ++ tailWord_1322707).sum := by decide
  have hdescent : baseEnd_1322707 < baseStart_1322707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322737 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 8]
def baseStart_1322737 : Nat := 118140960795 + 1322737 * 2 ^ 59
def prefixEnd_1322737 : Nat := 4983230072969 + 3 ^ 40 * 1322737 * 2
def baseEnd_1322737 : Nat := 75466651165144057678261

theorem tailTrace_1322737 : CollatzResearch.WordTrace tailWord_1322737 prefixEnd_1322737 75466651165144057678261 := by
  unfold tailWord_1322737
  simp only [CollatzResearch.WordTrace]
  refine ⟨48244181808957229339454465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32162787872638152892969643 48244181808957229339454465)
  ·
    refine ⟨36183136356717922004590849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48244181808957229339454465 36183136356717922004590849)
    ·
      refine ⟨27137352267538441503443137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36183136356717922004590849 27137352267538441503443137)
      ·
        refine ⟨20353014200653831127582353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27137352267538441503443137 20353014200653831127582353)
        ·
          refine ⟨15264760650490373345686765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20353014200653831127582353 15264760650490373345686765)
          ·
            refine ⟨5724285243933890004632537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15264760650490373345686765 5724285243933890004632537)
            ·
              refine ⟨4293213932950417503474403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5724285243933890004632537 4293213932950417503474403)
              ·
                refine ⟨6439820899425626255211605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293213932950417503474403 6439820899425626255211605)
                ·
                  refine ⟨75466651165144057678261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6439820899425626255211605 75466651165144057678261)
                  ·
                    rfl

theorem cell23_1322737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_1322737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322737 prefixEnd_1322737 := by exact prefixLift 1322737
  have htrace : WordTrace (prefixWord ++ tailWord_1322737) baseStart_1322737 baseEnd_1322737 := by
    simpa [prefixWord, tailWord_1322737, baseEnd_1322737] using wordTrace_append hprefix tailTrace_1322737
  have hstable : (prefixWord ++ tailWord_1322737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322737).length < 2 ^ (prefixWord ++ tailWord_1322737).sum := by decide
  have hdescent : baseEnd_1322737 < baseStart_1322737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322747 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 3]
def baseStart_1322747 : Nat := 118140960795 + 1322747 * 2 ^ 59
def prefixEnd_1322747 : Nat := 4983230072969 + 3 ^ 40 * 1322747 * 2
def baseEnd_1322747 : Nat := 679204995292841479979303

theorem tailTrace_1322747 : CollatzResearch.WordTrace tailWord_1322747 prefixEnd_1322747 679204995292841479979303 := by
  unfold tailWord_1322747
  simp only [CollatzResearch.WordTrace]
  refine ⟨48244546538921001047318495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32163031025947334031545663 48244546538921001047318495)
  ·
    refine ⟨72366819808381501570977743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48244546538921001047318495 72366819808381501570977743)
    ·
      refine ⟨108550229712572252356466615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72366819808381501570977743 108550229712572252356466615)
      ·
        refine ⟨162825344568858378534699923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108550229712572252356466615 162825344568858378534699923)
        ·
          refine ⟨244238016853287567802049885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162825344568858378534699923 244238016853287567802049885)
          ·
            refine ⟨91589256319982837925768707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244238016853287567802049885 91589256319982837925768707)
            ·
              refine ⟨137383884479974256888653061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91589256319982837925768707 137383884479974256888653061)
              ·
                refine ⟨25759478339995173166622449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137383884479974256888653061 25759478339995173166622449)
                ·
                  refine ⟨19319608754996379874966837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25759478339995173166622449 19319608754996379874966837)
                  ·
                    refine ⟨1811213320780910613278141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19319608754996379874966837 1811213320780910613278141)
                    ·
                      refine ⟨679204995292841479979303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1811213320780910613278141 679204995292841479979303)
                      ·
                        rfl

theorem cell23_1322747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 3].length) (baseStart_1322747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322747 prefixEnd_1322747 := by exact prefixLift 1322747
  have htrace : WordTrace (prefixWord ++ tailWord_1322747) baseStart_1322747 baseEnd_1322747 := by
    simpa [prefixWord, tailWord_1322747, baseEnd_1322747] using wordTrace_append hprefix tailTrace_1322747
  have hstable : (prefixWord ++ tailWord_1322747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322747).length < 2 ^ (prefixWord ++ tailWord_1322747).sum := by decide
  have hdescent : baseEnd_1322747 < baseStart_1322747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322841 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 3]
def baseStart_1322841 : Nat := 118140960795 + 1322841 * 2 ^ 59
def prefixEnd_1322841 : Nat := 4983230072969 + 3 ^ 40 * 1322841 * 2
def baseEnd_1322841 : Nat := 679253262474364112203871

theorem tailTrace_1322841 : CollatzResearch.WordTrace tailWord_1322841 prefixEnd_1322841 679253262474364112203871 := by
  unfold tailWord_1322841
  simp only [CollatzResearch.WordTrace]
  refine ⟨48247975000580455101240377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32165316667053636734160251 48247975000580455101240377)
  ·
    refine ⟨36185981250435341325930283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48247975000580455101240377 36185981250435341325930283)
    ·
      refine ⟨54278971875653011988895425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36185981250435341325930283 54278971875653011988895425)
      ·
        refine ⟨40709228906739758991671569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54278971875653011988895425 40709228906739758991671569)
        ·
          refine ⟨30531921680054819243753677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40709228906739758991671569 30531921680054819243753677)
          ·
            refine ⟨11449470630020557216407629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30531921680054819243753677 11449470630020557216407629)
            ·
              refine ⟨4293551486257708956152861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11449470630020557216407629 4293551486257708956152861)
              ·
                refine ⟨1610081807346640858557323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4293551486257708956152861 1610081807346640858557323)
                ·
                  refine ⟨2415122711019961287835985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610081807346640858557323 2415122711019961287835985)
                  ·
                    refine ⟨1811342033264970965876989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2415122711019961287835985 1811342033264970965876989)
                    ·
                      refine ⟨679253262474364112203871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1811342033264970965876989 679253262474364112203871)
                      ·
                        rfl

theorem cell23_1322841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_1322841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322841 prefixEnd_1322841 := by exact prefixLift 1322841
  have htrace : WordTrace (prefixWord ++ tailWord_1322841) baseStart_1322841 baseEnd_1322841 := by
    simpa [prefixWord, tailWord_1322841, baseEnd_1322841] using wordTrace_append hprefix tailTrace_1322841
  have hstable : (prefixWord ++ tailWord_1322841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322841).length < 2 ^ (prefixWord ++ tailWord_1322841).sum := by decide
  have hdescent : baseEnd_1322841 < baseStart_1322841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322848 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 2, 4]
def baseStart_1322848 : Nat := 118140960795 + 1322848 * 2 ^ 59
def prefixEnd_1322848 : Nat := 4983230072969 + 3 ^ 40 * 1322848 * 2
def baseEnd_1322848 : Nat := 226418952279648528272113

theorem tailTrace_1322848 : CollatzResearch.WordTrace tailWord_1322848 prefixEnd_1322848 226418952279648528272113 := by
  unfold tailWord_1322848
  simp only [CollatzResearch.WordTrace]
  refine ⟨24124115155777547648372599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32165486874370063531163465 24124115155777547648372599)
  ·
    refine ⟨36186172733666321472558899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24124115155777547648372599 36186172733666321472558899)
    ·
      refine ⟨54279259100499482208838349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36186172733666321472558899 54279259100499482208838349)
      ·
        refine ⟨20354722162687305828314381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54279259100499482208838349 20354722162687305828314381)
        ·
          refine ⟨7633020811007739685617893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20354722162687305828314381 7633020811007739685617893)
          ·
            refine ⟨1431191402063951191053355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7633020811007739685617893 1431191402063951191053355)
            ·
              refine ⟨2146787103095926786580033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431191402063951191053355 2146787103095926786580033)
              ·
                refine ⟨1610090327321945089935025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146787103095926786580033 1610090327321945089935025)
                ·
                  refine ⟨1207567745491458817451269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610090327321945089935025 1207567745491458817451269)
                  ·
                    refine ⟨226418952279648528272113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207567745491458817451269 226418952279648528272113)
                    ·
                      rfl

theorem cell23_1322848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_1322848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322848 prefixEnd_1322848 := by exact prefixLift 1322848
  have htrace : WordTrace (prefixWord ++ tailWord_1322848) baseStart_1322848 baseEnd_1322848 := by
    simpa [prefixWord, tailWord_1322848, baseEnd_1322848] using wordTrace_append hprefix tailTrace_1322848
  have hstable : (prefixWord ++ tailWord_1322848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322848).length < 2 ^ (prefixWord ++ tailWord_1322848).sum := by decide
  have hdescent : baseEnd_1322848 < baseStart_1322848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322855 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_1322855 : Nat := 118140960795 + 1322855 * 2 ^ 59
def prefixEnd_1322855 : Nat := 4983230072969 + 3 ^ 40 * 1322855 * 2
def baseEnd_1322855 : Nat := 679260451203527057428807

theorem tailTrace_1322855 : CollatzResearch.WordTrace tailWord_1322855 prefixEnd_1322855 679260451203527057428807 := by
  unfold tailWord_1322855
  simp only [CollatzResearch.WordTrace]
  refine ⟨48248485622529735492250019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32165657081686490328166679 48248485622529735492250019)
  ·
    refine ⟨72372728433794603238375029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48248485622529735492250019 72372728433794603238375029)
    ·
      refine ⟨6784943290668244053597659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72372728433794603238375029 6784943290668244053597659)
      ·
        refine ⟨10177414936002366080396489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784943290668244053597659 10177414936002366080396489)
        ·
          refine ⟨7633061202001774560297367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10177414936002366080396489 7633061202001774560297367)
          ·
            refine ⟨11449591803002661840446051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7633061202001774560297367 11449591803002661840446051)
            ·
              refine ⟨17174387704503992760669077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11449591803002661840446051 17174387704503992760669077)
              ·
                refine ⟨805049423648624660656363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17174387704503992760669077 805049423648624660656363)
                ·
                  refine ⟨1207574135472936990984545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805049423648624660656363 1207574135472936990984545)
                  ·
                    refine ⟨905680601604702743238409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1207574135472936990984545 905680601604702743238409)
                    ·
                      refine ⟨679260451203527057428807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905680601604702743238409 679260451203527057428807)
                      ·
                        rfl

theorem cell23_1322855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_1322855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322855 prefixEnd_1322855 := by exact prefixLift 1322855
  have htrace : WordTrace (prefixWord ++ tailWord_1322855) baseStart_1322855 baseEnd_1322855 := by
    simpa [prefixWord, tailWord_1322855, baseEnd_1322855] using wordTrace_append hprefix tailTrace_1322855
  have hstable : (prefixWord ++ tailWord_1322855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322855).length < 2 ^ (prefixWord ++ tailWord_1322855).sum := by decide
  have hdescent : baseEnd_1322855 < baseStart_1322855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322857 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_1322857 : Nat := 118140960795 + 1322857 * 2 ^ 59
def prefixEnd_1322857 : Nat := 4983230072969 + 3 ^ 40 * 1322857 * 2
def baseEnd_1322857 : Nat := 226420492721612016534599

theorem tailTrace_1322857 : CollatzResearch.WordTrace tailWord_1322857 prefixEnd_1322857 226420492721612016534599 := by
  unfold tailWord_1322857
  simp only [CollatzResearch.WordTrace]
  refine ⟨48248558568522489833822825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32165705712348326555881883 48248558568522489833822825)
  ·
    refine ⟨36186418926391867375367119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48248558568522489833822825 36186418926391867375367119)
    ·
      refine ⟨54279628389587801063050679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36186418926391867375367119 54279628389587801063050679)
      ·
        refine ⟨81419442584381701594576019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54279628389587801063050679 81419442584381701594576019)
        ·
          refine ⟨122129163876572552391864029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81419442584381701594576019 122129163876572552391864029)
          ·
            refine ⟨45798436453714707146949011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122129163876572552391864029 45798436453714707146949011)
            ·
              refine ⟨68697654680572060720423517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45798436453714707146949011 68697654680572060720423517)
              ·
                refine ⟨25761620505214522770158819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68697654680572060720423517 25761620505214522770158819)
                ·
                  refine ⟨38642430757821784155238229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25761620505214522770158819 38642430757821784155238229)
                  ·
                    refine ⟨226420492721612016534599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38642430757821784155238229 226420492721612016534599)
                    ·
                      rfl

theorem cell23_1322857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_1322857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322857 prefixEnd_1322857 := by exact prefixLift 1322857
  have htrace : WordTrace (prefixWord ++ tailWord_1322857) baseStart_1322857 baseEnd_1322857 := by
    simpa [prefixWord, tailWord_1322857, baseEnd_1322857] using wordTrace_append hprefix tailTrace_1322857
  have hstable : (prefixWord ++ tailWord_1322857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322857).length < 2 ^ (prefixWord ++ tailWord_1322857).sum := by decide
  have hdescent : baseEnd_1322857 < baseStart_1322857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322858 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1322858 : Nat := 118140960795 + 1322858 * 2 ^ 59
def prefixEnd_1322858 : Nat := 4983230072969 + 3 ^ 40 * 1322858 * 2
def baseEnd_1322858 : Nat := 679261991645490545691293

theorem tailTrace_1322858 : CollatzResearch.WordTrace tailWord_1322858 prefixEnd_1322858 679261991645490545691293 := by
  unfold tailWord_1322858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062148760379716751152307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32165730027679244669739485 12062148760379716751152307)
  ·
    refine ⟨18093223140569575126728461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12062148760379716751152307 18093223140569575126728461)
    ·
      refine ⟨6784958677713590672523173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18093223140569575126728461 6784958677713590672523173)
      ·
        refine ⟨1272179752071298251098095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6784958677713590672523173 1272179752071298251098095)
        ·
          refine ⟨1908269628106947376647143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272179752071298251098095 1908269628106947376647143)
          ·
            refine ⟨2862404442160421064970715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908269628106947376647143 2862404442160421064970715)
            ·
              refine ⟨4293606663240631597456073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862404442160421064970715 4293606663240631597456073)
              ·
                refine ⟨3220204997430473698092055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4293606663240631597456073 3220204997430473698092055)
                ·
                  refine ⟨4830307496145710547138083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220204997430473698092055 4830307496145710547138083)
                  ·
                    refine ⟨7245461244218565820707125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4830307496145710547138083 7245461244218565820707125)
                    ·
                      refine ⟨679261991645490545691293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7245461244218565820707125 679261991645490545691293)
                      ·
                        rfl

theorem cell23_1322858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1322858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322858 prefixEnd_1322858 := by exact prefixLift 1322858
  have htrace : WordTrace (prefixWord ++ tailWord_1322858) baseStart_1322858 baseEnd_1322858 := by
    simpa [prefixWord, tailWord_1322858, baseEnd_1322858] using wordTrace_append hprefix tailTrace_1322858
  have hstable : (prefixWord ++ tailWord_1322858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322858).length < 2 ^ (prefixWord ++ tailWord_1322858).sum := by decide
  have hdescent : baseEnd_1322858 < baseStart_1322858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322878 : List Nat := [4, 2, 3, 1, 1, 1, 4, 7]
def baseStart_1322878 : Nat := 118140960795 + 1322878 * 2 ^ 59
def prefixEnd_1322878 : Nat := 4983230072969 + 3 ^ 40 * 1322878 * 2
def baseEnd_1322878 : Nat := 25158231898465943238563

theorem tailTrace_1322878 : CollatzResearch.WordTrace tailWord_1322878 prefixEnd_1322878 25158231898465943238563 := by
  unfold tailWord_1322878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031165562680801302542161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32166216334297606946891525 6031165562680801302542161)
  ·
    refine ⟨4523374172010600976906621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6031165562680801302542161 4523374172010600976906621)
    ·
      refine ⟨1696265314503975366339983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4523374172010600976906621 1696265314503975366339983)
      ·
        refine ⟨2544397971755963049509975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696265314503975366339983 2544397971755963049509975)
        ·
          refine ⟨3816596957633944574264963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544397971755963049509975 3816596957633944574264963)
          ·
            refine ⟨5724895436450916861397445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816596957633944574264963 5724895436450916861397445)
            ·
              refine ⟨1073417894334546911512021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5724895436450916861397445 1073417894334546911512021)
              ·
                refine ⟨25158231898465943238563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1073417894334546911512021 25158231898465943238563)
                ·
                  rfl

theorem cell23_1322878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_1322878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322878 prefixEnd_1322878 := by exact prefixLift 1322878
  have htrace : WordTrace (prefixWord ++ tailWord_1322878) baseStart_1322878 baseEnd_1322878 := by
    simpa [prefixWord, tailWord_1322878, baseEnd_1322878] using wordTrace_append hprefix tailTrace_1322878
  have hstable : (prefixWord ++ tailWord_1322878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322878).length < 2 ^ (prefixWord ++ tailWord_1322878).sum := by decide
  have hdescent : baseEnd_1322878 < baseStart_1322878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322884 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1322884 : Nat := 118140960795 + 1322884 * 2 ^ 59
def prefixEnd_1322884 : Nat := 4983230072969 + 3 ^ 40 * 1322884 * 2
def baseEnd_1322884 : Nat := 679275342142507443966173

theorem tailTrace_1322884 : CollatzResearch.WordTrace tailWord_1322884 prefixEnd_1322884 679275342142507443966173 := by
  unfold tailWord_1322884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24124771669712336722527853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32166362226283115630037137 24124771669712336722527853)
  ·
    refine ⟨9046789376142126270947945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24124771669712336722527853 9046789376142126270947945)
    ·
      refine ⟨6785092032106594703210959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9046789376142126270947945 6785092032106594703210959)
      ·
        refine ⟨10177638048159892054816439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6785092032106594703210959 10177638048159892054816439)
        ·
          refine ⟨15266457072239838082224659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10177638048159892054816439 15266457072239838082224659)
          ·
            refine ⟨22899685608359757123336989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15266457072239838082224659 22899685608359757123336989)
            ·
              refine ⟨8587382103134908921251371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22899685608359757123336989 8587382103134908921251371)
              ·
                refine ⟨12881073154702363381877057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8587382103134908921251371 12881073154702363381877057)
                ·
                  refine ⟨9660804866026772536407793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12881073154702363381877057 9660804866026772536407793)
                  ·
                    refine ⟨7245603649520079402305845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9660804866026772536407793 7245603649520079402305845)
                    ·
                      refine ⟨679275342142507443966173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7245603649520079402305845 679275342142507443966173)
                      ·
                        rfl

theorem cell23_1322884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1322884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322884 prefixEnd_1322884 := by exact prefixLift 1322884
  have htrace : WordTrace (prefixWord ++ tailWord_1322884) baseStart_1322884 baseEnd_1322884 := by
    simpa [prefixWord, tailWord_1322884, baseEnd_1322884] using wordTrace_append hprefix tailTrace_1322884
  have hstable : (prefixWord ++ tailWord_1322884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322884).length < 2 ^ (prefixWord ++ tailWord_1322884).sum := by decide
  have hdescent : baseEnd_1322884 < baseStart_1322884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322926 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1322926 : Nat := 118140960795 + 1322926 * 2 ^ 59
def prefixEnd_1322926 : Nat := 4983230072969 + 3 ^ 40 * 1322926 * 2
def baseEnd_1322926 : Nat := 679296908329996279640981

theorem tailTrace_1322926 : CollatzResearch.WordTrace tailWord_1322926 prefixEnd_1322926 679296908329996279640981 := by
  unfold tailWord_1322926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031384400659064327260579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32167383470181676412056421 6031384400659064327260579)
  ·
    refine ⟨9047076600988596490890869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6031384400659064327260579 9047076600988596490890869)
    ·
      refine ⟨848163431342680921021019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9047076600988596490890869 848163431342680921021019)
      ·
        refine ⟨1272245147014021381531529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848163431342680921021019 1272245147014021381531529)
        ·
          refine ⟨954183860260516036148647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272245147014021381531529 954183860260516036148647)
          ·
            refine ⟨1431275790390774054222971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954183860260516036148647 1431275790390774054222971)
            ·
              refine ⟨2146913685586161081334457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431275790390774054222971 2146913685586161081334457)
              ·
                refine ⟨1610185264189620811000843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146913685586161081334457 1610185264189620811000843)
                ·
                  refine ⟨2415277896284431216501265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610185264189620811000843 2415277896284431216501265)
                  ·
                    refine ⟨1811458422213323412375949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2415277896284431216501265 1811458422213323412375949)
                    ·
                      refine ⟨679296908329996279640981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1811458422213323412375949 679296908329996279640981)
                      ·
                        rfl

theorem cell23_1322926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1322926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322926 prefixEnd_1322926 := by exact prefixLift 1322926
  have htrace : WordTrace (prefixWord ++ tailWord_1322926) baseStart_1322926 baseEnd_1322926 := by
    simpa [prefixWord, tailWord_1322926, baseEnd_1322926] using wordTrace_append hprefix tailTrace_1322926
  have hstable : (prefixWord ++ tailWord_1322926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322926).length < 2 ^ (prefixWord ++ tailWord_1322926).sum := by decide
  have hdescent : baseEnd_1322926 < baseStart_1322926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322932 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1322932 : Nat := 118140960795 + 1322932 * 2 ^ 59
def prefixEnd_1322932 : Nat := 4983230072969 + 3 ^ 40 * 1322932 * 2
def baseEnd_1322932 : Nat := 679299989213923256165953

theorem tailTrace_1322932 : CollatzResearch.WordTrace tailWord_1322932 prefixEnd_1322932 679299989213923256165953 := by
  unfold tailWord_1322932
  simp only [CollatzResearch.WordTrace]
  refine ⟨24125647021625388821401525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32167529362167185095202033 24125647021625388821401525)
  ·
    refine ⟨2261779408277380202006393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24125647021625388821401525 2261779408277380202006393)
    ·
      refine ⟨1696334556208035151504795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2261779408277380202006393 1696334556208035151504795)
      ·
        refine ⟨2544501834312052727257193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696334556208035151504795 2544501834312052727257193)
        ·
          refine ⟨1908376375734039545442895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2544501834312052727257193 1908376375734039545442895)
          ·
            refine ⟨2862564563601059318164343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908376375734039545442895 2862564563601059318164343)
            ·
              refine ⟨4293846845401588977246515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862564563601059318164343 4293846845401588977246515)
              ·
                refine ⟨6440770268102383465869773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293846845401588977246515 6440770268102383465869773)
                ·
                  refine ⟨2415288850538393799701165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6440770268102383465869773 2415288850538393799701165)
                  ·
                    refine ⟨905733318951897674887937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2415288850538393799701165 905733318951897674887937)
                    ·
                      refine ⟨679299989213923256165953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905733318951897674887937 679299989213923256165953)
                      ·
                        rfl

theorem cell23_1322932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1322932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322932 prefixEnd_1322932 := by exact prefixLift 1322932
  have htrace : WordTrace (prefixWord ++ tailWord_1322932) baseStart_1322932 baseEnd_1322932 := by
    simpa [prefixWord, tailWord_1322932, baseEnd_1322932] using wordTrace_append hprefix tailTrace_1322932
  have hstable : (prefixWord ++ tailWord_1322932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322932).length < 2 ^ (prefixWord ++ tailWord_1322932).sum := by decide
  have hdescent : baseEnd_1322932 < baseStart_1322932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322951 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 5]
def baseStart_1322951 : Nat := 118140960795 + 1322951 * 2 ^ 59
def prefixEnd_1322951 : Nat := 4983230072969 + 3 ^ 40 * 1322951 * 2
def baseEnd_1322951 : Nat := 75478860594039853536485

theorem tailTrace_1322951 : CollatzResearch.WordTrace tailWord_1322951 prefixEnd_1322951 75478860594039853536485 := by
  unfold tailWord_1322951
  simp only [CollatzResearch.WordTrace]
  refine ⟨48251987030181943887744707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32167991353454629258496471 48251987030181943887744707)
  ·
    refine ⟨72377980545272915831617061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48251987030181943887744707 72377980545272915831617061)
    ·
      refine ⟨13570871352238671718428199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72377980545272915831617061 13570871352238671718428199)
      ·
        refine ⟨20356307028358007577642299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13570871352238671718428199 20356307028358007577642299)
        ·
          refine ⟨30534460542537011366463449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20356307028358007577642299 30534460542537011366463449)
          ·
            refine ⟨22900845406902758524847587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30534460542537011366463449 22900845406902758524847587)
            ·
              refine ⟨34351268110354137787271381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22900845406902758524847587 34351268110354137787271381)
              ·
                refine ⟨805107846336425104389173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34351268110354137787271381 805107846336425104389173)
                ·
                  refine ⟨75478860594039853536485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805107846336425104389173 75478860594039853536485)
                  ·
                    rfl

theorem cell23_1322951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 5].length) (baseStart_1322951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322951 prefixEnd_1322951 := by exact prefixLift 1322951
  have htrace : WordTrace (prefixWord ++ tailWord_1322951) baseStart_1322951 baseEnd_1322951 := by
    simpa [prefixWord, tailWord_1322951, baseEnd_1322951] using wordTrace_append hprefix tailTrace_1322951
  have hstable : (prefixWord ++ tailWord_1322951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322951).length < 2 ^ (prefixWord ++ tailWord_1322951).sum := by decide
  have hdescent : baseEnd_1322951 < baseStart_1322951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322998 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1322998 : Nat := 118140960795 + 1322998 * 2 ^ 59
def prefixEnd_1322998 : Nat := 4983230072969 + 3 ^ 40 * 1322998 * 2
def baseEnd_1322998 : Nat := 226444626312373332646883

theorem tailTrace_1322998 : CollatzResearch.WordTrace tailWord_1322998 prefixEnd_1322998 226444626312373332646883 := by
  unfold tailWord_1322998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015856328813229432169103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32169134174007780609803765 3015856328813229432169103)
  ·
    refine ⟨4523784493219844148253655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3015856328813229432169103 4523784493219844148253655)
    ·
      refine ⟨6785676739829766222380483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4523784493219844148253655 6785676739829766222380483)
      ·
        refine ⟨10178515109744649333570725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6785676739829766222380483 10178515109744649333570725)
        ·
          refine ⟨1908471583077121750044511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10178515109744649333570725 1908471583077121750044511)
          ·
            refine ⟨2862707374615682625066767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908471583077121750044511 2862707374615682625066767)
            ·
              refine ⟨4294061061923523937600151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862707374615682625066767 4294061061923523937600151)
              ·
                refine ⟨6441091592885285906400227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294061061923523937600151 6441091592885285906400227)
                ·
                  refine ⟨9661637389327928859600341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6441091592885285906400227 9661637389327928859600341)
                  ·
                    refine ⟨226444626312373332646883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9661637389327928859600341 226444626312373332646883)
                    ·
                      rfl

theorem cell23_1322998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1322998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1322998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1322998 prefixEnd_1322998 := by exact prefixLift 1322998
  have htrace : WordTrace (prefixWord ++ tailWord_1322998) baseStart_1322998 baseEnd_1322998 := by
    simpa [prefixWord, tailWord_1322998, baseEnd_1322998] using wordTrace_append hprefix tailTrace_1322998
  have hstable : (prefixWord ++ tailWord_1322998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322998).length < 2 ^ (prefixWord ++ tailWord_1322998).sum := by decide
  have hdescent : baseEnd_1322998 < baseStart_1322998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323001 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1323001 : Nat := 118140960795 + 1323001 * 2 ^ 59
def prefixEnd_1323001 : Nat := 4983230072969 + 3 ^ 40 * 1323001 * 2
def baseEnd_1323001 : Nat := 679335419379083486203135

theorem tailTrace_1323001 : CollatzResearch.WordTrace tailWord_1323001 prefixEnd_1323001 679335419379083486203135 := by
  unfold tailWord_1323001
  simp only [CollatzResearch.WordTrace]
  refine ⟨48253810680000802427064857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32169207120000534951376571 48253810680000802427064857)
  ·
    refine ⟨36190358010000601820298643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48253810680000802427064857 36190358010000601820298643)
    ·
      refine ⟨54285537015000902730447965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36190358010000601820298643 54285537015000902730447965)
      ·
        refine ⟨20357076380625338523917987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54285537015000902730447965 20357076380625338523917987)
        ·
          refine ⟨30535614570938007785876981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20357076380625338523917987 30535614570938007785876981)
          ·
            refine ⟨2862713866025438229925967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30535614570938007785876981 2862713866025438229925967)
            ·
              refine ⟨4294070799038157344888951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862713866025438229925967 4294070799038157344888951)
              ·
                refine ⟨6441106198557236017333427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294070799038157344888951 6441106198557236017333427)
                ·
                  refine ⟨9661659297835854026000141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6441106198557236017333427 9661659297835854026000141)
                  ·
                    refine ⟨3623122236688445259750053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9661659297835854026000141 3623122236688445259750053)
                    ·
                      refine ⟨679335419379083486203135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3623122236688445259750053 679335419379083486203135)
                      ·
                        rfl

theorem cell23_1323001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1323001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323001 prefixEnd_1323001 := by exact prefixLift 1323001
  have htrace : WordTrace (prefixWord ++ tailWord_1323001) baseStart_1323001 baseEnd_1323001 := by
    simpa [prefixWord, tailWord_1323001, baseEnd_1323001] using wordTrace_append hprefix tailTrace_1323001
  have hstable : (prefixWord ++ tailWord_1323001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323001).length < 2 ^ (prefixWord ++ tailWord_1323001).sum := by decide
  have hdescent : baseEnd_1323001 < baseStart_1323001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323024 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 8]
def baseStart_1323024 : Nat := 118140960795 + 1323024 * 2 ^ 59
def prefixEnd_1323024 : Nat := 4983230072969 + 3 ^ 40 * 1323024 * 2
def baseEnd_1323024 : Nat := 75483025492681877357281

theorem tailTrace_1323024 : CollatzResearch.WordTrace tailWord_1323024 prefixEnd_1323024 75483025492681877357281 := by
  unfold tailWord_1323024
  simp only [CollatzResearch.WordTrace]
  refine ⟨24127324779458738677576063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32169766372611651570101417 24127324779458738677576063)
  ·
    refine ⟨36190987169188108016364095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24127324779458738677576063 36190987169188108016364095)
    ·
      refine ⟨54286480753782162024546143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36190987169188108016364095 54286480753782162024546143)
      ·
        refine ⟨81429721130673243036819215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54286480753782162024546143 81429721130673243036819215)
        ·
          refine ⟨122144581696009864555228823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81429721130673243036819215 122144581696009864555228823)
          ·
            refine ⟨183216872544014796832843235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122144581696009864555228823 183216872544014796832843235)
            ·
              refine ⟨274825308816022195249264853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183216872544014796832843235 274825308816022195249264853)
              ·
                refine ⟨6441218175375520201154645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 274825308816022195249264853 6441218175375520201154645)
                ·
                  refine ⟨75483025492681877357281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6441218175375520201154645 75483025492681877357281)
                  ·
                    rfl

theorem cell23_1323024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_1323024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323024 prefixEnd_1323024 := by exact prefixLift 1323024
  have htrace : WordTrace (prefixWord ++ tailWord_1323024) baseStart_1323024 baseEnd_1323024 := by
    simpa [prefixWord, tailWord_1323024, baseEnd_1323024] using wordTrace_append hprefix tailTrace_1323024
  have hstable : (prefixWord ++ tailWord_1323024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323024).length < 2 ^ (prefixWord ++ tailWord_1323024).sum := by decide
  have hdescent : baseEnd_1323024 < baseStart_1323024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323108 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_1323108 : Nat := 118140960795 + 1323108 * 2 ^ 59
def prefixEnd_1323108 : Nat := 4983230072969 + 3 ^ 40 * 1323108 * 2
def baseEnd_1323108 : Nat := 679390361809114567565143

theorem tailTrace_1323108 : CollatzResearch.WordTrace tailWord_1323108 prefixEnd_1323108 679390361809114567565143 := by
  unfold tailWord_1323108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24128856645306579850604989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32171808860408773134139985 24128856645306579850604989)
  ·
    refine ⟨9048321241989967443976871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24128856645306579850604989 9048321241989967443976871)
    ·
      refine ⟨13572481862984951165965307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9048321241989967443976871 13572481862984951165965307)
      ·
        refine ⟨20358722794477426748947961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13572481862984951165965307 20358722794477426748947961)
        ·
          refine ⟨15269042095858070061710971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20358722794477426748947961 15269042095858070061710971)
          ·
            refine ⟨22903563143787105092566457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15269042095858070061710971 22903563143787105092566457)
            ·
              refine ⟨17177672357840328819424843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22903563143787105092566457 17177672357840328819424843)
              ·
                refine ⟨25766508536760493229137265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17177672357840328819424843 25766508536760493229137265)
                ·
                  refine ⟨19324881402570369921852949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25766508536760493229137265 19324881402570369921852949)
                  ·
                    refine ⟨905853815745486090086857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19324881402570369921852949 905853815745486090086857)
                    ·
                      refine ⟨679390361809114567565143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905853815745486090086857 679390361809114567565143)
                      ·
                        rfl

theorem cell23_1323108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_1323108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323108 prefixEnd_1323108 := by exact prefixLift 1323108
  have htrace : WordTrace (prefixWord ++ tailWord_1323108) baseStart_1323108 baseEnd_1323108 := by
    simpa [prefixWord, tailWord_1323108, baseEnd_1323108] using wordTrace_append hprefix tailTrace_1323108
  have hstable : (prefixWord ++ tailWord_1323108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323108).length < 2 ^ (prefixWord ++ tailWord_1323108).sum := by decide
  have hdescent : baseEnd_1323108 < baseStart_1323108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323118 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1323118 : Nat := 118140960795 + 1323118 * 2 ^ 59
def prefixEnd_1323118 : Nat := 4983230072969 + 3 ^ 40 * 1323118 * 2
def baseEnd_1323118 : Nat := 226465165538553176146699

theorem tailTrace_1323118 : CollatzResearch.WordTrace tailWord_1323118 prefixEnd_1323118 226465165538553176146699 := by
  unfold tailWord_1323118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032259752572116426134251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32172052013717954272716005 6032259752572116426134251)
  ·
    refine ⟨9048389628858174639201377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6032259752572116426134251 9048389628858174639201377)
    ·
      refine ⟨6786292221643630979401033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9048389628858174639201377 6786292221643630979401033)
      ·
        refine ⟨5089719166232723234550775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6786292221643630979401033 5089719166232723234550775)
        ·
          refine ⟨7634578749349084851826163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5089719166232723234550775 7634578749349084851826163)
          ·
            refine ⟨11451868124023627277739245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634578749349084851826163 11451868124023627277739245)
            ·
              refine ⟨4294450546508860229152217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11451868124023627277739245 4294450546508860229152217)
              ·
                refine ⟨3220837909881645171864163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4294450546508860229152217 3220837909881645171864163)
                ·
                  refine ⟨4831256864822467757796245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220837909881645171864163 4831256864822467757796245)
                  ·
                    refine ⟨226465165538553176146699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4831256864822467757796245 226465165538553176146699)
                    ·
                      rfl

theorem cell23_1323118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1323118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323118 prefixEnd_1323118 := by exact prefixLift 1323118
  have htrace : WordTrace (prefixWord ++ tailWord_1323118) baseStart_1323118 baseEnd_1323118 := by
    simpa [prefixWord, tailWord_1323118, baseEnd_1323118] using wordTrace_append hprefix tailTrace_1323118
  have hstable : (prefixWord ++ tailWord_1323118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323118).length < 2 ^ (prefixWord ++ tailWord_1323118).sum := by decide
  have hdescent : baseEnd_1323118 < baseStart_1323118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323248 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_1323248 : Nat := 118140960795 + 1323248 * 2 ^ 59
def prefixEnd_1323248 : Nat := 4983230072969 + 3 ^ 40 * 1323248 * 2
def baseEnd_1323248 : Nat := 679462249100744019814499

theorem tailTrace_1323248 : CollatzResearch.WordTrace tailWord_1323248 prefixEnd_1323248 679462249100744019814499 := by
  unfold tailWord_1323248
  simp only [CollatzResearch.WordTrace]
  refine ⟨24131409755052981805653199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32175213006737309074204265 24131409755052981805653199)
  ·
    refine ⟨36197114632579472708479799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24131409755052981805653199 36197114632579472708479799)
    ·
      refine ⟨54295671948869209062719699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36197114632579472708479799 54295671948869209062719699)
      ·
        refine ⟨81443507923303813594079549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54295671948869209062719699 81443507923303813594079549)
        ·
          refine ⟨30541315471238930097779831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81443507923303813594079549 30541315471238930097779831)
          ·
            refine ⟨45811973206858395146669747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30541315471238930097779831 45811973206858395146669747)
            ·
              refine ⟨68717959810287592720004621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45811973206858395146669747 68717959810287592720004621)
              ·
                refine ⟨25769234928857847270001733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68717959810287592720004621 25769234928857847270001733)
                ·
                  refine ⟨4831731549160846363125325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25769234928857847270001733 4831731549160846363125325)
                  ·
                    refine ⟨1811899330935317386171997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4831731549160846363125325 1811899330935317386171997)
                    ·
                      refine ⟨679462249100744019814499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1811899330935317386171997 679462249100744019814499)
                      ·
                        rfl

theorem cell23_1323248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_1323248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323248 prefixEnd_1323248 := by exact prefixLift 1323248
  have htrace : WordTrace (prefixWord ++ tailWord_1323248) baseStart_1323248 baseEnd_1323248 := by
    simpa [prefixWord, tailWord_1323248, baseEnd_1323248] using wordTrace_append hprefix tailTrace_1323248
  have hstable : (prefixWord ++ tailWord_1323248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323248).length < 2 ^ (prefixWord ++ tailWord_1323248).sum := by decide
  have hdescent : baseEnd_1323248 < baseStart_1323248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323266 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_1323266 : Nat := 118140960795 + 1323266 * 2 ^ 59
def prefixEnd_1323266 : Nat := 4983230072969 + 3 ^ 40 * 1323266 * 2
def baseEnd_1323266 : Nat := 679471491752524949389417

theorem tailTrace_1323266 : CollatzResearch.WordTrace tailWord_1323266 prefixEnd_1323266 679471491752524949389417 := by
  unfold tailWord_1323266
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065869006010188171365413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32175650682693835123641101 12065869006010188171365413)
  ·
    refine ⟨2262350438626910282131015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12065869006010188171365413 2262350438626910282131015)
    ·
      refine ⟨3393525657940365423196523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262350438626910282131015 3393525657940365423196523)
      ·
        refine ⟨5090288486910548134794785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393525657940365423196523 5090288486910548134794785)
        ·
          refine ⟨3817716365182911101096089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5090288486910548134794785 3817716365182911101096089)
          ·
            refine ⟨2863287273887183325822067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3817716365182911101096089 2863287273887183325822067)
            ·
              refine ⟨4294930910830774988733101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863287273887183325822067 4294930910830774988733101)
              ·
                refine ⟨1610599091561540620774913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4294930910830774988733101 1610599091561540620774913)
                ·
                  refine ⟨1207949318671155465581185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610599091561540620774913 1207949318671155465581185)
                  ·
                    refine ⟨905961989003366599185889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1207949318671155465581185 905961989003366599185889)
                    ·
                      refine ⟨679471491752524949389417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 905961989003366599185889 679471491752524949389417)
                      ·
                        rfl

theorem cell23_1323266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_1323266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323266 prefixEnd_1323266 := by exact prefixLift 1323266
  have htrace : WordTrace (prefixWord ++ tailWord_1323266) baseStart_1323266 baseEnd_1323266 := by
    simpa [prefixWord, tailWord_1323266, baseEnd_1323266] using wordTrace_append hprefix tailTrace_1323266
  have hstable : (prefixWord ++ tailWord_1323266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323266).length < 2 ^ (prefixWord ++ tailWord_1323266).sum := by decide
  have hdescent : baseEnd_1323266 < baseStart_1323266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323278 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1323278 : Nat := 118140960795 + 1323278 * 2 ^ 59
def prefixEnd_1323278 : Nat := 4983230072969 + 3 ^ 40 * 1323278 * 2
def baseEnd_1323278 : Nat := 679477653520378902439361

theorem tailTrace_1323278 : CollatzResearch.WordTrace tailWord_1323278 prefixEnd_1323278 679477653520378902439361 := by
  unfold tailWord_1323278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032989212499659841862311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32175942466664852489932325 6032989212499659841862311)
  ·
    refine ⟨9049483818749489762793467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6032989212499659841862311 9049483818749489762793467)
    ·
      refine ⟨13574225728124234644190201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9049483818749489762793467 13574225728124234644190201)
      ·
        refine ⟨10180669296093175983142651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13574225728124234644190201 10180669296093175983142651)
        ·
          refine ⟨15271003944139763974713977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10180669296093175983142651 15271003944139763974713977)
          ·
            refine ⟨11453252958104822981035483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15271003944139763974713977 11453252958104822981035483)
            ·
              refine ⟨17179879437157234471553225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11453252958104822981035483 17179879437157234471553225)
              ·
                refine ⟨12884909577867925853664919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17179879437157234471553225 12884909577867925853664919)
                ·
                  refine ⟨19327364366801888780497379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12884909577867925853664919 19327364366801888780497379)
                  ·
                    refine ⟨28991046550202833170746069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19327364366801888780497379 28991046550202833170746069)
                    ·
                      refine ⟨679477653520378902439361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28991046550202833170746069 679477653520378902439361)
                      ·
                        rfl

theorem cell23_1323278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1323278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323278 prefixEnd_1323278 := by exact prefixLift 1323278
  have htrace : WordTrace (prefixWord ++ tailWord_1323278) baseStart_1323278 baseEnd_1323278 := by
    simpa [prefixWord, tailWord_1323278, baseEnd_1323278] using wordTrace_append hprefix tailTrace_1323278
  have hstable : (prefixWord ++ tailWord_1323278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323278).length < 2 ^ (prefixWord ++ tailWord_1323278).sum := by decide
  have hdescent : baseEnd_1323278 < baseStart_1323278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323306 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_1323306 : Nat := 118140960795 + 1323306 * 2 ^ 59
def prefixEnd_1323306 : Nat := 4983230072969 + 3 ^ 40 * 1323306 * 2
def baseEnd_1323306 : Nat := 75499114553189421432137

theorem tailTrace_1323306 : CollatzResearch.WordTrace tailWord_1323306 prefixEnd_1323306 75499114553189421432137 := by
  unfold tailWord_1323306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12066233735973959879229443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32176623295930559677945181 12066233735973959879229443)
  ·
    refine ⟨18099350603960939818844165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12066233735973959879229443 18099350603960939818844165)
    ·
      refine ⟨3393628238242676216033281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18099350603960939818844165 3393628238242676216033281)
      ·
        refine ⟨2545221178682007162024961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3393628238242676216033281 2545221178682007162024961)
        ·
          refine ⟨1908915884011505371518721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2545221178682007162024961 1908915884011505371518721)
          ·
            refine ⟨1431686913008629028639041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1908915884011505371518721 1431686913008629028639041)
            ·
              refine ⟨1073765184756471771479281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431686913008629028639041 1073765184756471771479281)
              ·
                refine ⟨805323888567353828609461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073765184756471771479281 805323888567353828609461)
                ·
                  refine ⟨75499114553189421432137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805323888567353828609461 75499114553189421432137)
                  ·
                    rfl

theorem cell23_1323306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_1323306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323306 prefixEnd_1323306 := by exact prefixLift 1323306
  have htrace : WordTrace (prefixWord ++ tailWord_1323306) baseStart_1323306 baseEnd_1323306 := by
    simpa [prefixWord, tailWord_1323306, baseEnd_1323306] using wordTrace_append hprefix tailTrace_1323306
  have hstable : (prefixWord ++ tailWord_1323306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323306).length < 2 ^ (prefixWord ++ tailWord_1323306).sum := by decide
  have hdescent : baseEnd_1323306 < baseStart_1323306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323315 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 3, 4]
def baseStart_1323315 : Nat := 118140960795 + 1323315 * 2 ^ 59
def prefixEnd_1323315 : Nat := 4983230072969 + 3 ^ 40 * 1323315 * 2
def baseEnd_1323315 : Nat := 226498884101531752558897

theorem tailTrace_1323315 : CollatzResearch.WordTrace tailWord_1323315 prefixEnd_1323315 226498884101531752558897 := by
  unfold tailWord_1323315
  simp only [CollatzResearch.WordTrace]
  refine ⟨48265263200863234053995399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32176842133908822702663599 48265263200863234053995399)
  ·
    refine ⟨72397894801294851080993099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48265263200863234053995399 72397894801294851080993099)
    ·
      refine ⟨108596842201942276621489649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72397894801294851080993099 108596842201942276621489649)
      ·
        refine ⟨81447631651456707466117237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108596842201942276621489649 81447631651456707466117237)
        ·
          refine ⟨7635715467324066324948491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81447631651456707466117237 7635715467324066324948491)
          ·
            refine ⟨11453573200986099487422737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635715467324066324948491 11453573200986099487422737)
            ·
              refine ⟨8590179900739574615567053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11453573200986099487422737 8590179900739574615567053)
              ·
                refine ⟨3221317462777340480837645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8590179900739574615567053 3221317462777340480837645)
                ·
                  refine ⟨1207994048541502680314117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3221317462777340480837645 1207994048541502680314117)
                  ·
                    refine ⟨226498884101531752558897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207994048541502680314117 226498884101531752558897)
                    ·
                      rfl

theorem cell23_1323315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 4].length) (baseStart_1323315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323315 prefixEnd_1323315 := by exact prefixLift 1323315
  have htrace : WordTrace (prefixWord ++ tailWord_1323315) baseStart_1323315 baseEnd_1323315 := by
    simpa [prefixWord, tailWord_1323315, baseEnd_1323315] using wordTrace_append hprefix tailTrace_1323315
  have hstable : (prefixWord ++ tailWord_1323315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323315).length < 2 ^ (prefixWord ++ tailWord_1323315).sum := by decide
  have hdescent : baseEnd_1323315 < baseStart_1323315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323322 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2]
def baseStart_1323322 : Nat := 118140960795 + 1323322 * 2 ^ 59
def prefixEnd_1323322 : Nat := 4983230072969 + 3 ^ 40 * 1323322 * 2
def baseEnd_1323322 : Nat := 679500246669176730289159

theorem tailTrace_1323322 : CollatzResearch.WordTrace tailWord_1323322 prefixEnd_1323322 679500246669176730289159 := by
  unfold tailWord_1323322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12066379627959468562375055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32177012341225249499666813 12066379627959468562375055)
  ·
    refine ⟨18099569441939202843562583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12066379627959468562375055 18099569441939202843562583)
    ·
      refine ⟨27149354162908804265343875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18099569441939202843562583 27149354162908804265343875)
      ·
        refine ⟨40724031244363206398015813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27149354162908804265343875 40724031244363206398015813)
        ·
          refine ⟨7635755858318101199627965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40724031244363206398015813 7635755858318101199627965)
          ·
            refine ⟨2863408446869287949860487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7635755858318101199627965 2863408446869287949860487)
            ·
              refine ⟨4295112670303931924790731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863408446869287949860487 4295112670303931924790731)
              ·
                refine ⟨6442669005455897887186097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295112670303931924790731 6442669005455897887186097)
                ·
                  refine ⟨4832001754091923415389573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6442669005455897887186097 4832001754091923415389573)
                  ·
                    refine ⟨906000328892235640385545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832001754091923415389573 906000328892235640385545)
                    ·
                      refine ⟨679500246669176730289159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906000328892235640385545 679500246669176730289159)
                      ·
                        rfl

theorem cell23_1323322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_1323322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323322 prefixEnd_1323322 := by exact prefixLift 1323322
  have htrace : WordTrace (prefixWord ++ tailWord_1323322) baseStart_1323322 baseEnd_1323322 := by
    simpa [prefixWord, tailWord_1323322, baseEnd_1323322] using wordTrace_append hprefix tailTrace_1323322
  have hstable : (prefixWord ++ tailWord_1323322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323322).length < 2 ^ (prefixWord ++ tailWord_1323322).sum := by decide
  have hdescent : baseEnd_1323322 < baseStart_1323322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323362 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1323362 : Nat := 118140960795 + 1323362 * 2 ^ 59
def prefixEnd_1323362 : Nat := 4983230072969 + 3 ^ 40 * 1323362 * 2
def baseEnd_1323362 : Nat := 75502309543928508198775

theorem tailTrace_1323362 : CollatzResearch.WordTrace tailWord_1323362 prefixEnd_1323362 75502309543928508198775 := by
  unfold tailWord_1323362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12066744357923240270239085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32177984954461974053970893 12066744357923240270239085)
  ·
    refine ⟨4525029134221215101339657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12066744357923240270239085 4525029134221215101339657)
    ·
      refine ⟨3393771850665911326004743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4525029134221215101339657 3393771850665911326004743)
      ·
        refine ⟨5090657775998866989007115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393771850665911326004743 5090657775998866989007115)
        ·
          refine ⟨7635986663998300483510673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5090657775998866989007115 7635986663998300483510673)
          ·
            refine ⟨5726989997998725362633005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7635986663998300483510673 5726989997998725362633005)
            ·
              refine ⟨2147621249249522010987377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5726989997998725362633005 2147621249249522010987377)
              ·
                refine ⟨1610715936937141508240533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147621249249522010987377 1610715936937141508240533)
                ·
                  refine ⟨75502309543928508198775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1610715936937141508240533 75502309543928508198775)
                  ·
                    rfl

theorem cell23_1323362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1323362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323362 prefixEnd_1323362 := by exact prefixLift 1323362
  have htrace : WordTrace (prefixWord ++ tailWord_1323362) baseStart_1323362 baseEnd_1323362 := by
    simpa [prefixWord, tailWord_1323362, baseEnd_1323362] using wordTrace_append hprefix tailTrace_1323362
  have hstable : (prefixWord ++ tailWord_1323362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323362).length < 2 ^ (prefixWord ++ tailWord_1323362).sum := by decide
  have hdescent : baseEnd_1323362 < baseStart_1323362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323408 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1323408 : Nat := 118140960795 + 1323408 * 2 ^ 59
def prefixEnd_1323408 : Nat := 4983230072969 + 3 ^ 40 * 1323408 * 2
def baseEnd_1323408 : Nat := 679544406005463393813763

theorem tailTrace_1323408 : CollatzResearch.WordTrace tailWord_1323408 prefixEnd_1323408 679544406005463393813763 := by
  unfold tailWord_1323408
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134327594763155468565439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32179103459684207291420585 24134327594763155468565439)
  ·
    refine ⟨36201491392144733202848159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24134327594763155468565439 36201491392144733202848159)
    ·
      refine ⟨54302237088217099804272239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36201491392144733202848159 54302237088217099804272239)
      ·
        refine ⟨81453355632325649706408359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54302237088217099804272239 81453355632325649706408359)
        ·
          refine ⟨122180033448488474559612539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81453355632325649706408359 122180033448488474559612539)
          ·
            refine ⟨183270050172732711839418809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122180033448488474559612539 183270050172732711839418809)
            ·
              refine ⟨137452537629549533879564107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183270050172732711839418809 137452537629549533879564107)
              ·
                refine ⟨206178806444324300819346161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137452537629549533879564107 206178806444324300819346161)
                ·
                  refine ⟨154634104833243225614509621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206178806444324300819346161 154634104833243225614509621)
                  ·
                    refine ⟨14496947328116552401360277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154634104833243225614509621 14496947328116552401360277)
                    ·
                      refine ⟨679544406005463393813763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14496947328116552401360277 679544406005463393813763)
                      ·
                        rfl

theorem cell23_1323408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1323408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323408 prefixEnd_1323408 := by exact prefixLift 1323408
  have htrace : WordTrace (prefixWord ++ tailWord_1323408) baseStart_1323408 baseEnd_1323408 := by
    simpa [prefixWord, tailWord_1323408, baseEnd_1323408] using wordTrace_append hprefix tailTrace_1323408
  have hstable : (prefixWord ++ tailWord_1323408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323408).length < 2 ^ (prefixWord ++ tailWord_1323408).sum := by decide
  have hdescent : baseEnd_1323408 < baseStart_1323408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323415 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1323415 : Nat := 118140960795 + 1323415 * 2 ^ 59
def prefixEnd_1323415 : Nat := 4983230072969 + 3 ^ 40 * 1323415 * 2
def baseEnd_1323415 : Nat := 679548000370044866426231

theorem tailTrace_1323415 : CollatzResearch.WordTrace tailWord_1323415 prefixEnd_1323415 679548000370044866426231 := by
  unfold tailWord_1323415
  simp only [CollatzResearch.WordTrace]
  refine ⟨48268910500500951132635699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32179273667000634088423799 48268910500500951132635699)
  ·
    refine ⟨72403365750751426698953549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48268910500500951132635699 72403365750751426698953549)
    ·
      refine ⟨27151262156531785012107581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72403365750751426698953549 27151262156531785012107581)
      ·
        refine ⟨10181723308699419379540343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27151262156531785012107581 10181723308699419379540343)
        ·
          refine ⟨15272584963049129069310515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10181723308699419379540343 15272584963049129069310515)
          ·
            refine ⟨22908877444573693603965773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15272584963049129069310515 22908877444573693603965773)
            ·
              refine ⟨8590829041715135101487165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22908877444573693603965773 8590829041715135101487165)
              ·
                refine ⟨3221560890643175663057687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8590829041715135101487165 3221560890643175663057687)
                ·
                  refine ⟨4832341335964763494586531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221560890643175663057687 4832341335964763494586531)
                  ·
                    refine ⟨7248512003947145241879797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832341335964763494586531 7248512003947145241879797)
                    ·
                      refine ⟨679548000370044866426231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7248512003947145241879797 679548000370044866426231)
                      ·
                        rfl

theorem cell23_1323415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1323415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323415 prefixEnd_1323415 := by exact prefixLift 1323415
  have htrace : WordTrace (prefixWord ++ tailWord_1323415) baseStart_1323415 baseEnd_1323415 := by
    simpa [prefixWord, tailWord_1323415, baseEnd_1323415] using wordTrace_append hprefix tailTrace_1323415
  have hstable : (prefixWord ++ tailWord_1323415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323415).length < 2 ^ (prefixWord ++ tailWord_1323415).sum := by decide
  have hdescent : baseEnd_1323415 < baseStart_1323415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323449 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1323449 : Nat := 118140960795 + 1323449 * 2 ^ 59
def prefixEnd_1323449 : Nat := 4983230072969 + 3 ^ 40 * 1323449 * 2
def baseEnd_1323449 : Nat := 679565458712297733401075

theorem tailTrace_1323449 : CollatzResearch.WordTrace tailWord_1323449 prefixEnd_1323449 679565458712297733401075 := by
  unfold tailWord_1323449
  simp only [CollatzResearch.WordTrace]
  refine ⟨48270150582377774939373401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32180100388251849959582267 48270150582377774939373401)
  ·
    refine ⟨36202612936783331204530051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48270150582377774939373401 36202612936783331204530051)
    ·
      refine ⟨54303919405174996806795077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36202612936783331204530051 54303919405174996806795077)
      ·
        refine ⟨10181984888470311901274077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54303919405174996806795077 10181984888470311901274077)
        ·
          refine ⟨3818244333176366962977779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10181984888470311901274077 3818244333176366962977779)
          ·
            refine ⟨5727366499764550444466669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818244333176366962977779 5727366499764550444466669)
            ·
              refine ⟨2147762437411706416675001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5727366499764550444466669 2147762437411706416675001)
              ·
                refine ⟨1610821828058779812506251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147762437411706416675001 1610821828058779812506251)
                ·
                  refine ⟨2416232742088169718759377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610821828058779812506251 2416232742088169718759377)
                  ·
                    refine ⟨1812174556566127289069533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416232742088169718759377 1812174556566127289069533)
                    ·
                      refine ⟨679565458712297733401075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812174556566127289069533 679565458712297733401075)
                      ·
                        rfl

theorem cell23_1323449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1323449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323449 prefixEnd_1323449 := by exact prefixLift 1323449
  have htrace : WordTrace (prefixWord ++ tailWord_1323449) baseStart_1323449 baseEnd_1323449 := by
    simpa [prefixWord, tailWord_1323449, baseEnd_1323449] using wordTrace_append hprefix tailTrace_1323449
  have hstable : (prefixWord ++ tailWord_1323449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323449).length < 2 ^ (prefixWord ++ tailWord_1323449).sum := by decide
  have hdescent : baseEnd_1323449 < baseStart_1323449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323472 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 7, 3, 2]
def baseStart_1323472 : Nat := 118140960795 + 1323472 * 2 ^ 59
def prefixEnd_1323472 : Nat := 4983230072969 + 3 ^ 40 * 1323472 * 2
def baseEnd_1323472 : Nat := 679577268767351143413469

theorem tailTrace_1323472 : CollatzResearch.WordTrace tailWord_1323472 prefixEnd_1323472 679577268767351143413469 := by
  unfold tailWord_1323472
  simp only [CollatzResearch.WordTrace]
  refine ⟨24135494730647224933730335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32180659640862966578307113 24135494730647224933730335)
  ·
    refine ⟨36203242095970837400595503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24135494730647224933730335 36203242095970837400595503)
    ·
      refine ⟨54304863143956256100893255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36203242095970837400595503 54304863143956256100893255)
      ·
        refine ⟨81457294715934384151339883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54304863143956256100893255 81457294715934384151339883)
        ·
          refine ⟨122185942073901576227009825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81457294715934384151339883 122185942073901576227009825)
          ·
            refine ⟨91639456555426182170257369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122185942073901576227009825 91639456555426182170257369)
            ·
              refine ⟨68729592416569636627693027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91639456555426182170257369 68729592416569636627693027)
              ·
                refine ⟨103094388624854454941539541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68729592416569636627693027 103094388624854454941539541)
                ·
                  refine ⟨2416274733395026287692333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 103094388624854454941539541 2416274733395026287692333)
                  ·
                    refine ⟨906103025023134857884625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2416274733395026287692333 906103025023134857884625)
                    ·
                      refine ⟨679577268767351143413469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906103025023134857884625 679577268767351143413469)
                      ·
                        rfl

theorem cell23_1323472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 3, 2].length) (baseStart_1323472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323472 prefixEnd_1323472 := by exact prefixLift 1323472
  have htrace : WordTrace (prefixWord ++ tailWord_1323472) baseStart_1323472 baseEnd_1323472 := by
    simpa [prefixWord, tailWord_1323472, baseEnd_1323472] using wordTrace_append hprefix tailTrace_1323472
  have hstable : (prefixWord ++ tailWord_1323472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323472).length < 2 ^ (prefixWord ++ tailWord_1323472).sum := by decide
  have hdescent : baseEnd_1323472 < baseStart_1323472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323515 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4]
def baseStart_1323515 : Nat := 118140960795 + 1323515 * 2 ^ 59
def prefixEnd_1323515 : Nat := 4983230072969 + 3 ^ 40 * 1323515 * 2
def baseEnd_1323515 : Nat := 679599348435494475175771

theorem tailTrace_1323515 : CollatzResearch.WordTrace tailWord_1323515 prefixEnd_1323515 679599348435494475175771 := by
  unfold tailWord_1323515
  simp only [CollatzResearch.WordTrace]
  refine ⟨48272557800138668211275999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32181705200092445474183999 48272557800138668211275999)
  ·
    refine ⟨72408836700208002316913999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48272557800138668211275999 72408836700208002316913999)
    ·
      refine ⟨108613255050312003475370999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72408836700208002316913999 108613255050312003475370999)
      ·
        refine ⟨162919882575468005213056499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108613255050312003475370999 162919882575468005213056499)
        ·
          refine ⟨244379823863202007819584749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162919882575468005213056499 244379823863202007819584749)
          ·
            refine ⟨91642433948700752932344281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244379823863202007819584749 91642433948700752932344281)
            ·
              refine ⟨68731825461525564699258211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91642433948700752932344281 68731825461525564699258211)
              ·
                refine ⟨103097738192288347048887317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68731825461525564699258211 103097738192288347048887317)
                ·
                  refine ⟨4832706477763516267916593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103097738192288347048887317 4832706477763516267916593)
                  ·
                    refine ⟨3624529858322637200937445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832706477763516267916593 3624529858322637200937445)
                    ·
                      refine ⟨679599348435494475175771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3624529858322637200937445 679599348435494475175771)
                      ·
                        rfl

theorem cell23_1323515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_1323515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323515 prefixEnd_1323515 := by exact prefixLift 1323515
  have htrace : WordTrace (prefixWord ++ tailWord_1323515) baseStart_1323515 baseEnd_1323515 := by
    simpa [prefixWord, tailWord_1323515, baseEnd_1323515] using wordTrace_append hprefix tailTrace_1323515
  have hstable : (prefixWord ++ tailWord_1323515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323515).length < 2 ^ (prefixWord ++ tailWord_1323515).sum := by decide
  have hdescent : baseEnd_1323515 < baseStart_1323515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323519 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 4, 2, 2]
def baseStart_1323519 : Nat := 118140960795 + 1323519 * 2 ^ 59
def prefixEnd_1323519 : Nat := 4983230072969 + 3 ^ 40 * 1323519 * 2
def baseEnd_1323519 : Nat := 679601402358112459525753

theorem tailTrace_1323519 : CollatzResearch.WordTrace tailWord_1323519 prefixEnd_1323519 679601402358112459525753 := by
  unfold tailWord_1323519
  simp only [CollatzResearch.WordTrace]
  refine ⟨48272703692124176894421611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32181802461416117929614407 48272703692124176894421611)
  ·
    refine ⟨72409055538186265341632417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48272703692124176894421611 72409055538186265341632417)
    ·
      refine ⟨54306791653639699006224313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72409055538186265341632417 54306791653639699006224313)
      ·
        refine ⟨40730093740229774254668235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54306791653639699006224313 40730093740229774254668235)
        ·
          refine ⟨61095140610344661382002353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40730093740229774254668235 61095140610344661382002353)
          ·
            refine ⟨45821355457758496036501765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61095140610344661382002353 45821355457758496036501765)
            ·
              refine ⟨8591504148329718006844081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45821355457758496036501765 8591504148329718006844081)
              ·
                refine ⟨6443628111247288505133061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8591504148329718006844081 6443628111247288505133061)
                ·
                  refine ⟨1208180270858866594712449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6443628111247288505133061 1208180270858866594712449)
                  ·
                    refine ⟨906135203144149946034337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1208180270858866594712449 906135203144149946034337)
                    ·
                      refine ⟨679601402358112459525753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906135203144149946034337 679601402358112459525753)
                      ·
                        rfl

theorem cell23_1323519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_1323519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323519 prefixEnd_1323519 := by exact prefixLift 1323519
  have htrace : WordTrace (prefixWord ++ tailWord_1323519) baseStart_1323519 baseEnd_1323519 := by
    simpa [prefixWord, tailWord_1323519, baseEnd_1323519] using wordTrace_append hprefix tailTrace_1323519
  have hstable : (prefixWord ++ tailWord_1323519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323519).length < 2 ^ (prefixWord ++ tailWord_1323519).sum := by decide
  have hdescent : baseEnd_1323519 < baseStart_1323519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323532 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1323532 : Nat := 118140960795 + 1323532 * 2 ^ 59
def prefixEnd_1323532 : Nat := 4983230072969 + 3 ^ 40 * 1323532 * 2
def baseEnd_1323532 : Nat := 679608077606620908663193

theorem tailTrace_1323532 : CollatzResearch.WordTrace tailWord_1323532 prefixEnd_1323532 679608077606620908663193 := by
  unfold tailWord_1323532
  simp only [CollatzResearch.WordTrace]
  refine ⟨24136588920538540057322425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32182118560718053409763233 24136588920538540057322425)
  ·
    refine ⟨18102441690403905042991819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24136588920538540057322425 18102441690403905042991819)
    ·
      refine ⟨27153662535605857564487729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18102441690403905042991819 27153662535605857564487729)
      ·
        refine ⟨20365246901704393173365797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27153662535605857564487729 20365246901704393173365797)
        ·
          refine ⟨3818483794069573720006087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20365246901704393173365797 3818483794069573720006087)
          ·
            refine ⟨5727725691104360580009131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818483794069573720006087 5727725691104360580009131)
            ·
              refine ⟨8591588536656540870013697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727725691104360580009131 8591588536656540870013697)
              ·
                refine ⟨6443691402492405652510273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8591588536656540870013697 6443691402492405652510273)
                ·
                  refine ⟨4832768551869304239382705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443691402492405652510273 4832768551869304239382705)
                  ·
                    refine ⟨3624576413901978179537029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832768551869304239382705 3624576413901978179537029)
                    ·
                      refine ⟨679608077606620908663193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3624576413901978179537029 679608077606620908663193)
                      ·
                        rfl

theorem cell23_1323532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1323532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323532 prefixEnd_1323532 := by exact prefixLift 1323532
  have htrace : WordTrace (prefixWord ++ tailWord_1323532) baseStart_1323532 baseEnd_1323532 := by
    simpa [prefixWord, tailWord_1323532, baseEnd_1323532] using wordTrace_append hprefix tailTrace_1323532
  have hstable : (prefixWord ++ tailWord_1323532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323532).length < 2 ^ (prefixWord ++ tailWord_1323532).sum := by decide
  have hdescent : baseEnd_1323532 < baseStart_1323532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323553 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_1323553 : Nat := 118140960795 + 1323553 * 2 ^ 59
def prefixEnd_1323553 : Nat := 4983230072969 + 3 ^ 40 * 1323553 * 2
def baseEnd_1323553 : Nat := 679618860700365326500597

theorem tailTrace_1323553 : CollatzResearch.WordTrace tailWord_1323553 prefixEnd_1323553 679618860700365326500597 := by
  unfold tailWord_1323553
  simp only [CollatzResearch.WordTrace]
  refine ⟨48273943774001000701159313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32182629182667333800772875 48273943774001000701159313)
  ·
    refine ⟨36205457830500750525869485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48273943774001000701159313 36205457830500750525869485)
    ·
      refine ⟨13577046686437781447201057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36205457830500750525869485 13577046686437781447201057)
      ·
        refine ⟨10182785014828336085400793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13577046686437781447201057 10182785014828336085400793)
        ·
          refine ⟨7637088761121252064050595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10182785014828336085400793 7637088761121252064050595)
          ·
            refine ⟨11455633141681878096075893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7637088761121252064050595 11455633141681878096075893)
            ·
              refine ⟨1073965607032676071507115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11455633141681878096075893 1073965607032676071507115)
              ·
                refine ⟨1610948410549014107260673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073965607032676071507115 1610948410549014107260673)
                ·
                  refine ⟨1208211307911760580445505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610948410549014107260673 1208211307911760580445505)
                  ·
                    refine ⟨906158480933820435334129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1208211307911760580445505 906158480933820435334129)
                    ·
                      refine ⟨679618860700365326500597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906158480933820435334129 679618860700365326500597)
                      ·
                        rfl

theorem cell23_1323553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_1323553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323553 prefixEnd_1323553 := by exact prefixLift 1323553
  have htrace : WordTrace (prefixWord ++ tailWord_1323553) baseStart_1323553 baseEnd_1323553 := by
    simpa [prefixWord, tailWord_1323553, baseEnd_1323553] using wordTrace_append hprefix tailTrace_1323553
  have hstable : (prefixWord ++ tailWord_1323553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323553).length < 2 ^ (prefixWord ++ tailWord_1323553).sum := by decide
  have hdescent : baseEnd_1323553 < baseStart_1323553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323642 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_1323642 : Nat := 118140960795 + 1323642 * 2 ^ 59
def prefixEnd_1323642 : Nat := 4983230072969 + 3 ^ 40 * 1323642 * 2
def baseEnd_1323642 : Nat := 679664560478615478287687

theorem tailTrace_1323642 : CollatzResearch.WordTrace tailWord_1323642 prefixEnd_1323642 679664560478615478287687 := by
  unfold tailWord_1323642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069297467669642225287295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32184793247119045934099453 12069297467669642225287295)
  ·
    refine ⟨18103946201504463337930943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12069297467669642225287295 18103946201504463337930943)
    ·
      refine ⟨27155919302256695006896415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18103946201504463337930943 27155919302256695006896415)
      ·
        refine ⟨40733878953385042510344623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27155919302256695006896415 40733878953385042510344623)
        ·
          refine ⟨61100818430077563765516935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40733878953385042510344623 61100818430077563765516935)
          ·
            refine ⟨91651227645116345648275403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61100818430077563765516935 91651227645116345648275403)
            ·
              refine ⟨137476841467674518472413105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91651227645116345648275403 137476841467674518472413105)
              ·
                refine ⟨103107631100755888854309829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137476841467674518472413105 103107631100755888854309829)
                ·
                  refine ⟨19332680831391729160183093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103107631100755888854309829 19332680831391729160183093)
                  ·
                    refine ⟨1812438827942974608767165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19332680831391729160183093 1812438827942974608767165)
                    ·
                      refine ⟨679664560478615478287687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812438827942974608767165 679664560478615478287687)
                      ·
                        rfl

theorem cell23_1323642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_1323642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323642 prefixEnd_1323642 := by exact prefixLift 1323642
  have htrace : WordTrace (prefixWord ++ tailWord_1323642) baseStart_1323642 baseEnd_1323642 := by
    simpa [prefixWord, tailWord_1323642, baseEnd_1323642] using wordTrace_append hprefix tailTrace_1323642
  have hstable : (prefixWord ++ tailWord_1323642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323642).length < 2 ^ (prefixWord ++ tailWord_1323642).sum := by decide
  have hdescent : baseEnd_1323642 < baseStart_1323642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323649 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 6]
def baseStart_1323649 : Nat := 118140960795 + 1323649 * 2 ^ 59
def prefixEnd_1323649 : Nat := 4983230072969 + 3 ^ 40 * 1323649 * 2
def baseEnd_1323649 : Nat := 75518683871466327877795

theorem tailTrace_1323649 : CollatzResearch.WordTrace tailWord_1323649 prefixEnd_1323649 75518683871466327877795 := by
  unfold tailWord_1323649
  simp only [CollatzResearch.WordTrace]
  refine ⟨48277445181653209096654001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32184963454435472731102667 48277445181653209096654001)
  ·
    refine ⟨36208083886239906822490501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48277445181653209096654001 36208083886239906822490501)
    ·
      refine ⟨6789015728669982529216969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36208083886239906822490501 6789015728669982529216969)
      ·
        refine ⟨5091761796502486896912727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6789015728669982529216969 5091761796502486896912727)
        ·
          refine ⟨7637642694753730345369091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091761796502486896912727 7637642694753730345369091)
          ·
            refine ⟨11456464042130595518053637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7637642694753730345369091 11456464042130595518053637)
            ·
              refine ⟨2148087007899486659635057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11456464042130595518053637 2148087007899486659635057)
              ·
                refine ⟨1611065255924614994726293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148087007899486659635057 1611065255924614994726293)
                ·
                  refine ⟨75518683871466327877795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1611065255924614994726293 75518683871466327877795)
                  ·
                    rfl

theorem cell23_1323649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 6].length) (baseStart_1323649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323649 prefixEnd_1323649 := by exact prefixLift 1323649
  have htrace : WordTrace (prefixWord ++ tailWord_1323649) baseStart_1323649 baseEnd_1323649 := by
    simpa [prefixWord, tailWord_1323649, baseEnd_1323649] using wordTrace_append hprefix tailTrace_1323649
  have hstable : (prefixWord ++ tailWord_1323649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323649).length < 2 ^ (prefixWord ++ tailWord_1323649).sum := by decide
  have hdescent : baseEnd_1323649 < baseStart_1323649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323653 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_1323653 : Nat := 118140960795 + 1323653 * 2 ^ 59
def prefixEnd_1323653 : Nat := 4983230072969 + 3 ^ 40 * 1323653 * 2
def baseEnd_1323653 : Nat := 226556736255271645083379

theorem tailTrace_1323653 : CollatzResearch.WordTrace tailWord_1323653 prefixEnd_1323653 226556736255271645083379 := by
  unfold tailWord_1323653
  simp only [CollatzResearch.WordTrace]
  refine ⟨48277591073638717779799613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32185060715759145186533075 48277591073638717779799613)
  ·
    refine ⟨18104096652614519167424855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48277591073638717779799613 18104096652614519167424855)
    ·
      refine ⟨27156144978921778751137283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18104096652614519167424855 27156144978921778751137283)
      ·
        refine ⟨40734217468382668126705925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27156144978921778751137283 40734217468382668126705925)
        ·
          refine ⟨7637665775321750273757361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40734217468382668126705925 7637665775321750273757361)
          ·
            refine ⟨5728249331491312705318021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637665775321750273757361 5728249331491312705318021)
            ·
              refine ⟨1074046749654621132247129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5728249331491312705318021 1074046749654621132247129)
              ·
                refine ⟨805535062240965849185347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074046749654621132247129 805535062240965849185347)
                ·
                  refine ⟨1208302593361448773778021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805535062240965849185347 1208302593361448773778021)
                  ·
                    refine ⟨226556736255271645083379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208302593361448773778021 226556736255271645083379)
                    ·
                      rfl

theorem cell23_1323653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_1323653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323653 prefixEnd_1323653 := by exact prefixLift 1323653
  have htrace : WordTrace (prefixWord ++ tailWord_1323653) baseStart_1323653 baseEnd_1323653 := by
    simpa [prefixWord, tailWord_1323653, baseEnd_1323653] using wordTrace_append hprefix tailTrace_1323653
  have hstable : (prefixWord ++ tailWord_1323653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323653).length < 2 ^ (prefixWord ++ tailWord_1323653).sum := by decide
  have hdescent : baseEnd_1323653 < baseStart_1323653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323672 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1323672 : Nat := 118140960795 + 1323672 * 2 ^ 59
def prefixEnd_1323672 : Nat := 4983230072969 + 3 ^ 40 * 1323672 * 2
def baseEnd_1323672 : Nat := 679679964898250360912549

theorem tailTrace_1323672 : CollatzResearch.WordTrace tailWord_1323672 prefixEnd_1323672 679679964898250360912549 := by
  unfold tailWord_1323672
  simp only [CollatzResearch.WordTrace]
  refine ⟨24139142030284942012370635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32185522707046589349827513 24139142030284942012370635)
  ·
    refine ⟨36208713045427413018555953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24139142030284942012370635 36208713045427413018555953)
    ·
      refine ⟨27156534784070559763916965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36208713045427413018555953 27156534784070559763916965)
      ·
        refine ⟨5091850272013229955734431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27156534784070559763916965 5091850272013229955734431)
        ·
          refine ⟨7637775408019844933601647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091850272013229955734431 7637775408019844933601647)
          ·
            refine ⟨11456663112029767400402471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7637775408019844933601647 11456663112029767400402471)
            ·
              refine ⟨17184994668044651100603707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11456663112029767400402471 17184994668044651100603707)
              ·
                refine ⟨25777492002066976650905561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17184994668044651100603707 25777492002066976650905561)
                ·
                  refine ⟨19333119001550232488179171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25777492002066976650905561 19333119001550232488179171)
                  ·
                    refine ⟨28999678502325348732268757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19333119001550232488179171 28999678502325348732268757)
                    ·
                      refine ⟨679679964898250360912549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28999678502325348732268757 679679964898250360912549)
                      ·
                        rfl

theorem cell23_1323672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1323672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323672 prefixEnd_1323672 := by exact prefixLift 1323672
  have htrace : WordTrace (prefixWord ++ tailWord_1323672) baseStart_1323672 baseEnd_1323672 := by
    simpa [prefixWord, tailWord_1323672, baseEnd_1323672] using wordTrace_append hprefix tailTrace_1323672
  have hstable : (prefixWord ++ tailWord_1323672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323672).length < 2 ^ (prefixWord ++ tailWord_1323672).sum := by decide
  have hdescent : baseEnd_1323672 < baseStart_1323672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323676 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1323676 : Nat := 118140960795 + 1323676 * 2 ^ 59
def prefixEnd_1323676 : Nat := 4983230072969 + 3 ^ 40 * 1323676 * 2
def baseEnd_1323676 : Nat := 679682018820868345262531

theorem tailTrace_1323676 : CollatzResearch.WordTrace tailWord_1323676 prefixEnd_1323676 679682018820868345262531 := by
  unfold tailWord_1323676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24139214976277696353943441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32185619968370261805257921 24139214976277696353943441)
  ·
    refine ⟨18104411232208272265457581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24139214976277696353943441 18104411232208272265457581)
    ·
      refine ⟨6789154212078102099546593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18104411232208272265457581 6789154212078102099546593)
      ·
        refine ⟨5091865659058576574659945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6789154212078102099546593 5091865659058576574659945)
        ·
          refine ⟨3818899244293932430994959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5091865659058576574659945 3818899244293932430994959)
          ·
            refine ⟨5728348866440898646492439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818899244293932430994959 5728348866440898646492439)
            ·
              refine ⟨8592523299661347969738659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728348866440898646492439 8592523299661347969738659)
              ·
                refine ⟨12888784949492021954607989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8592523299661347969738659 12888784949492021954607989)
                ·
                  refine ⟨1208323589014877058244499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12888784949492021954607989 1208323589014877058244499)
                  ·
                    refine ⟨1812485383522315587366749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1208323589014877058244499 1812485383522315587366749)
                    ·
                      refine ⟨679682018820868345262531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812485383522315587366749 679682018820868345262531)
                      ·
                        rfl

theorem cell23_1323676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1323676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323676 prefixEnd_1323676 := by exact prefixLift 1323676
  have htrace : WordTrace (prefixWord ++ tailWord_1323676) baseStart_1323676 baseEnd_1323676 := by
    simpa [prefixWord, tailWord_1323676, baseEnd_1323676] using wordTrace_append hprefix tailTrace_1323676
  have hstable : (prefixWord ++ tailWord_1323676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323676).length < 2 ^ (prefixWord ++ tailWord_1323676).sum := by decide
  have hdescent : baseEnd_1323676 < baseStart_1323676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323719 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1323719 : Nat := 118140960795 + 1323719 * 2 ^ 59
def prefixEnd_1323719 : Nat := 4983230072969 + 3 ^ 40 * 1323719 * 2
def baseEnd_1323719 : Nat := 679704098489011677024833

theorem tailTrace_1323719 : CollatzResearch.WordTrace tailWord_1323719 prefixEnd_1323719 679704098489011677024833 := by
  unfold tailWord_1323719
  simp only [CollatzResearch.WordTrace]
  refine ⟨48279998291399611051702211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32186665527599740701134807 48279998291399611051702211)
  ·
    refine ⟨72419997437099416577553317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48279998291399611051702211 72419997437099416577553317)
    ·
      refine ⟨13578749519456140608291247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72419997437099416577553317 13578749519456140608291247)
      ·
        refine ⟨20368124279184210912436871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13578749519456140608291247 20368124279184210912436871)
        ·
          refine ⟨30552186418776316368655307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20368124279184210912436871 30552186418776316368655307)
          ·
            refine ⟨45828279628164474552982961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30552186418776316368655307 45828279628164474552982961)
            ·
              refine ⟨34371209721123355914737221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45828279628164474552982961 34371209721123355914737221)
              ·
                refine ⟨6444601822710629234013229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34371209721123355914737221 6444601822710629234013229)
                ·
                  refine ⟨2416725683516485962754961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6444601822710629234013229 2416725683516485962754961)
                  ·
                    refine ⟨1812544262637364472066221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416725683516485962754961 1812544262637364472066221)
                    ·
                      refine ⟨679704098489011677024833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812544262637364472066221 679704098489011677024833)
                      ·
                        rfl

theorem cell23_1323719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1323719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323719 prefixEnd_1323719 := by exact prefixLift 1323719
  have htrace : WordTrace (prefixWord ++ tailWord_1323719) baseStart_1323719 baseEnd_1323719 := by
    simpa [prefixWord, tailWord_1323719, baseEnd_1323719] using wordTrace_append hprefix tailTrace_1323719
  have hstable : (prefixWord ++ tailWord_1323719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323719).length < 2 ^ (prefixWord ++ tailWord_1323719).sum := by decide
  have hdescent : baseEnd_1323719 < baseStart_1323719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323726 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_1323726 : Nat := 118140960795 + 1323726 * 2 ^ 59
def prefixEnd_1323726 : Nat := 4983230072969 + 3 ^ 40 * 1323726 * 2
def baseEnd_1323726 : Nat := 226569230951197716545767

theorem tailTrace_1323726 : CollatzResearch.WordTrace tailWord_1323726 prefixEnd_1323726 226569230951197716545767 := by
  unfold tailWord_1323726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035031700296781405900879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32186835734916167498138021 6035031700296781405900879)
  ·
    refine ⟨9052547550445172108851319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6035031700296781405900879 9052547550445172108851319)
    ·
      refine ⟨13578821325667758163276979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9052547550445172108851319 13578821325667758163276979)
      ·
        refine ⟨20368231988501637244915469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13578821325667758163276979 20368231988501637244915469)
        ·
          refine ⟨7638086995688113966843301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20368231988501637244915469 7638086995688113966843301)
          ·
            refine ⟨1432141311691521368783119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7638086995688113966843301 1432141311691521368783119)
            ·
              refine ⟨2148211967537282053174679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432141311691521368783119 2148211967537282053174679)
              ·
                refine ⟨3222317951305923079762019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148211967537282053174679 3222317951305923079762019)
                ·
                  refine ⟨4833476926958884619643029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222317951305923079762019 4833476926958884619643029)
                  ·
                    refine ⟨226569230951197716545767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4833476926958884619643029 226569230951197716545767)
                    ·
                      rfl

theorem cell23_1323726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_1323726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323726 prefixEnd_1323726 := by exact prefixLift 1323726
  have htrace : WordTrace (prefixWord ++ tailWord_1323726) baseStart_1323726 baseEnd_1323726 := by
    simpa [prefixWord, tailWord_1323726, baseEnd_1323726] using wordTrace_append hprefix tailTrace_1323726
  have hstable : (prefixWord ++ tailWord_1323726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323726).length < 2 ^ (prefixWord ++ tailWord_1323726).sum := by decide
  have hdescent : baseEnd_1323726 < baseStart_1323726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323736 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_1323736 : Nat := 118140960795 + 1323736 * 2 ^ 59
def prefixEnd_1323736 : Nat := 4983230072969 + 3 ^ 40 * 1323736 * 2
def baseEnd_1323736 : Nat := 679712827660138110512255

theorem tailTrace_1323736 : CollatzResearch.WordTrace tailWord_1323736 prefixEnd_1323736 679712827660138110512255 := by
  unfold tailWord_1323736
  simp only [CollatzResearch.WordTrace]
  refine ⟨24140309166169011477535531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32187078888225348636714041 24140309166169011477535531)
  ·
    refine ⟨36210463749253517216303297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24140309166169011477535531 36210463749253517216303297)
    ·
      refine ⟨27157847811940137912227473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36210463749253517216303297 27157847811940137912227473)
      ·
        refine ⟨20368385858955103434170605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27157847811940137912227473 20368385858955103434170605)
        ·
          refine ⟨7638144697108163787813977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20368385858955103434170605 7638144697108163787813977)
          ·
            refine ⟨5728608522831122840860483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7638144697108163787813977 5728608522831122840860483)
            ·
              refine ⟨8592912784246684261290725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728608522831122840860483 8592912784246684261290725)
              ·
                refine ⟨1611171147046253298992011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8592912784246684261290725 1611171147046253298992011)
                ·
                  refine ⟨2416756720569379948488017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611171147046253298992011 2416756720569379948488017)
                  ·
                    refine ⟨1812567540427034961366013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416756720569379948488017 1812567540427034961366013)
                    ·
                      refine ⟨679712827660138110512255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812567540427034961366013 679712827660138110512255)
                      ·
                        rfl

theorem cell23_1323736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_1323736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323736 prefixEnd_1323736 := by exact prefixLift 1323736
  have htrace : WordTrace (prefixWord ++ tailWord_1323736) baseStart_1323736 baseEnd_1323736 := by
    simpa [prefixWord, tailWord_1323736, baseEnd_1323736] using wordTrace_append hprefix tailTrace_1323736
  have hstable : (prefixWord ++ tailWord_1323736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323736).length < 2 ^ (prefixWord ++ tailWord_1323736).sum := by decide
  have hdescent : baseEnd_1323736 < baseStart_1323736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323792 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1323792 : Nat := 118140960795 + 1323792 * 2 ^ 59
def prefixEnd_1323792 : Nat := 4983230072969 + 3 ^ 40 * 1323792 * 2
def baseEnd_1323792 : Nat := 679741582576789891411997

theorem tailTrace_1323792 : CollatzResearch.WordTrace tailWord_1323792 prefixEnd_1323792 679741582576789891411997 := by
  unfold tailWord_1323792
  simp only [CollatzResearch.WordTrace]
  refine ⟨24141330410067572259554815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32188440546756763012739753 24141330410067572259554815)
  ·
    refine ⟨36211995615101358389332223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24141330410067572259554815 36211995615101358389332223)
    ·
      refine ⟨54317993422652037583998335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36211995615101358389332223 54317993422652037583998335)
      ·
        refine ⟨81476990133978056375997503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54317993422652037583998335 81476990133978056375997503)
        ·
          refine ⟨122215485200967084563996255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81476990133978056375997503 122215485200967084563996255)
          ·
            refine ⟨183323227801450626845994383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122215485200967084563996255 183323227801450626845994383)
            ·
              refine ⟨274984841702175940268991575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183323227801450626845994383 274984841702175940268991575)
              ·
                refine ⟨412477262553263910403487363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274984841702175940268991575 412477262553263910403487363)
                ·
                  refine ⟨618715893829895865605231045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412477262553263910403487363 618715893829895865605231045)
                  ·
                    refine ⟨116009230093105474800980821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618715893829895865605231045 116009230093105474800980821)
                    ·
                      refine ⟨679741582576789891411997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 116009230093105474800980821 679741582576789891411997)
                      ·
                        rfl

theorem cell23_1323792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1323792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323792 prefixEnd_1323792 := by exact prefixLift 1323792
  have htrace : WordTrace (prefixWord ++ tailWord_1323792) baseStart_1323792 baseEnd_1323792 := by
    simpa [prefixWord, tailWord_1323792, baseEnd_1323792] using wordTrace_append hprefix tailTrace_1323792
  have hstable : (prefixWord ++ tailWord_1323792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323792).length < 2 ^ (prefixWord ++ tailWord_1323792).sum := by decide
  have hdescent : baseEnd_1323792 < baseStart_1323792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323793 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 1, 3, 2]
def baseStart_1323793 : Nat := 118140960795 + 1323793 * 2 ^ 59
def prefixEnd_1323793 : Nat := 4983230072969 + 3 ^ 40 * 1323793 * 2
def baseEnd_1323793 : Nat := 679742096057444387499493

theorem tailTrace_1323793 : CollatzResearch.WordTrace tailWord_1323793 prefixEnd_1323793 679742096057444387499493 := by
  unfold tailWord_1323793
  simp only [CollatzResearch.WordTrace]
  refine ⟨48282697293131521689896033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32188464862087681126597355 48282697293131521689896033)
  ·
    refine ⟨36212022969848641267422025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48282697293131521689896033 36212022969848641267422025)
    ·
      refine ⟨27159017227386480950566519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36212022969848641267422025 27159017227386480950566519)
      ·
        refine ⟨40738525841079721425849779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27159017227386480950566519 40738525841079721425849779)
        ·
          refine ⟨61107788761619582138774669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40738525841079721425849779 61107788761619582138774669)
          ·
            refine ⟨22915420785607343302040501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61107788761619582138774669 22915420785607343302040501)
            ·
              refine ⟨2148320698650688434566297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22915420785607343302040501 2148320698650688434566297)
              ·
                refine ⟨1611240523988016325924723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148320698650688434566297 1611240523988016325924723)
                ·
                  refine ⟨2416860785982024488887085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611240523988016325924723 2416860785982024488887085)
                  ·
                    refine ⟨906322794743259183332657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2416860785982024488887085 906322794743259183332657)
                    ·
                      refine ⟨679742096057444387499493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906322794743259183332657 679742096057444387499493)
                      ·
                        rfl

theorem cell23_1323793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_1323793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323793 prefixEnd_1323793 := by exact prefixLift 1323793
  have htrace : WordTrace (prefixWord ++ tailWord_1323793) baseStart_1323793 baseEnd_1323793 := by
    simpa [prefixWord, tailWord_1323793, baseEnd_1323793] using wordTrace_append hprefix tailTrace_1323793
  have hstable : (prefixWord ++ tailWord_1323793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323793).length < 2 ^ (prefixWord ++ tailWord_1323793).sum := by decide
  have hdescent : baseEnd_1323793 < baseStart_1323793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323809 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1323809 : Nat := 118140960795 + 1323809 * 2 ^ 59
def prefixEnd_1323809 : Nat := 4983230072969 + 3 ^ 40 * 1323809 * 2
def baseEnd_1323809 : Nat := 679750311747916324899419

theorem tailTrace_1323809 : CollatzResearch.WordTrace tailWord_1323809 prefixEnd_1323809 679750311747916324899419 := by
  unfold tailWord_1323809
  simp only [CollatzResearch.WordTrace]
  refine ⟨48283280861073556422478481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32188853907382370948318987 48283280861073556422478481)
  ·
    refine ⟨36212460645805167316858861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48283280861073556422478481 36212460645805167316858861)
    ·
      refine ⟨13579672742176937743822073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36212460645805167316858861 13579672742176937743822073)
      ·
        refine ⟨10184754556632703307866555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13579672742176937743822073 10184754556632703307866555)
        ·
          refine ⟨15277131834949054961799833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10184754556632703307866555 15277131834949054961799833)
          ·
            refine ⟨11457848876211791221349875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15277131834949054961799833 11457848876211791221349875)
            ·
              refine ⟨17186773314317686832024813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11457848876211791221349875 17186773314317686832024813)
              ·
                refine ⟨6445039992869132562009305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17186773314317686832024813 6445039992869132562009305)
                ·
                  refine ⟨4833779994651849421506979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6445039992869132562009305 4833779994651849421506979)
                  ·
                    refine ⟨7250669991977774132260469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833779994651849421506979 7250669991977774132260469)
                    ·
                      refine ⟨679750311747916324899419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7250669991977774132260469 679750311747916324899419)
                      ·
                        rfl

theorem cell23_1323809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1323809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323809 prefixEnd_1323809 := by exact prefixLift 1323809
  have htrace : WordTrace (prefixWord ++ tailWord_1323809) baseStart_1323809 baseEnd_1323809 := by
    simpa [prefixWord, tailWord_1323809, baseEnd_1323809] using wordTrace_append hprefix tailTrace_1323809
  have hstable : (prefixWord ++ tailWord_1323809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323809).length < 2 ^ (prefixWord ++ tailWord_1323809).sum := by decide
  have hdescent : baseEnd_1323809 < baseStart_1323809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323818 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1323818 : Nat := 118140960795 + 1323818 * 2 ^ 59
def prefixEnd_1323818 : Nat := 4983230072969 + 3 ^ 40 * 1323818 * 2
def baseEnd_1323818 : Nat := 679754933073806789686879

theorem tailTrace_1323818 : CollatzResearch.WordTrace tailWord_1323818 prefixEnd_1323818 679754933073806789686879 := by
  unfold tailWord_1323818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12070902279510237739889027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32189072745360633973037405 12070902279510237739889027)
  ·
    refine ⟨18106353419265356609833541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12070902279510237739889027 18106353419265356609833541)
    ·
      refine ⟨3394941266112254364343789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18106353419265356609833541 3394941266112254364343789)
      ·
        refine ⟨1273102974792095386628921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3394941266112254364343789 1273102974792095386628921)
        ·
          refine ⟨954827231094071539971691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1273102974792095386628921 954827231094071539971691)
          ·
            refine ⟨1432240846641107309957537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954827231094071539971691 1432240846641107309957537)
            ·
              refine ⟨1074180634980830482468153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432240846641107309957537 1074180634980830482468153)
              ·
                refine ⟨805635476235622861851115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074180634980830482468153 805635476235622861851115)
                ·
                  refine ⟨1208453214353434292776673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805635476235622861851115 1208453214353434292776673)
                  ·
                    refine ⟨906339910765075719582505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1208453214353434292776673 906339910765075719582505)
                    ·
                      refine ⟨679754933073806789686879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906339910765075719582505 679754933073806789686879)
                      ·
                        rfl

theorem cell23_1323818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1323818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323818 prefixEnd_1323818 := by exact prefixLift 1323818
  have htrace : WordTrace (prefixWord ++ tailWord_1323818) baseStart_1323818 baseEnd_1323818 := by
    simpa [prefixWord, tailWord_1323818, baseEnd_1323818] using wordTrace_append hprefix tailTrace_1323818
  have hstable : (prefixWord ++ tailWord_1323818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323818).length < 2 ^ (prefixWord ++ tailWord_1323818).sum := by decide
  have hdescent : baseEnd_1323818 < baseStart_1323818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323863 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 5]
def baseStart_1323863 : Nat := 118140960795 + 1323863 * 2 ^ 59
def prefixEnd_1323863 : Nat := 4983230072969 + 3 ^ 40 * 1323863 * 2
def baseEnd_1323863 : Nat := 75530893300362123736019

theorem tailTrace_1323863 : CollatzResearch.WordTrace tailWord_1323863 prefixEnd_1323863 75530893300362123736019 := by
  unfold tailWord_1323863
  simp only [CollatzResearch.WordTrace]
  refine ⟨48285250402877923644944243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32190166935251949096629495 48285250402877923644944243)
  ·
    refine ⟨72427875604316885467416365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48285250402877923644944243 72427875604316885467416365)
    ·
      refine ⟨27160453351618832050281137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72427875604316885467416365 27160453351618832050281137)
      ·
        refine ⟨20370340013714124037710853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27160453351618832050281137 20370340013714124037710853)
        ·
          refine ⟨3819438752571398257070785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20370340013714124037710853 3819438752571398257070785)
          ·
            refine ⟨2864579064428548692803089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3819438752571398257070785 2864579064428548692803089)
            ·
              refine ⟨2148434298321411519602317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2864579064428548692803089 2148434298321411519602317)
              ·
                refine ⟨805662861870529319850869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2148434298321411519602317 805662861870529319850869)
                ·
                  refine ⟨75530893300362123736019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805662861870529319850869 75530893300362123736019)
                  ·
                    rfl

theorem cell23_1323863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 5].length) (baseStart_1323863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323863 prefixEnd_1323863 := by exact prefixLift 1323863
  have htrace : WordTrace (prefixWord ++ tailWord_1323863) baseStart_1323863 baseEnd_1323863 := by
    simpa [prefixWord, tailWord_1323863, baseEnd_1323863] using wordTrace_append hprefix tailTrace_1323863
  have hstable : (prefixWord ++ tailWord_1323863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323863).length < 2 ^ (prefixWord ++ tailWord_1323863).sum := by decide
  have hdescent : baseEnd_1323863 < baseStart_1323863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323874 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1323874 : Nat := 118140960795 + 1323874 * 2 ^ 59
def prefixEnd_1323874 : Nat := 4983230072969 + 3 ^ 40 * 1323874 * 2
def baseEnd_1323874 : Nat := 679783687990458570586621

theorem tailTrace_1323874 : CollatzResearch.WordTrace tailWord_1323874 prefixEnd_1323874 679783687990458570586621 := by
  unfold tailWord_1323874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12071412901459518130898669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32190434403892048349063117 12071412901459518130898669)
  ·
    refine ⟨4526779838047319299087001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12071412901459518130898669 4526779838047319299087001)
    ·
      refine ⟨3395084878535489474315251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4526779838047319299087001 3395084878535489474315251)
      ·
        refine ⟨5092627317803234211472877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3395084878535489474315251 5092627317803234211472877)
        ·
          refine ⟨1909735244176212829302329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5092627317803234211472877 1909735244176212829302329)
          ·
            refine ⟨1432301433132159621976747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1909735244176212829302329 1432301433132159621976747)
            ·
              refine ⟨2148452149698239432965121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432301433132159621976747 2148452149698239432965121)
              ·
                refine ⟨1611339112273679574723841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148452149698239432965121 1611339112273679574723841)
                ·
                  refine ⟨1208504334205259681042881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1611339112273679574723841 1208504334205259681042881)
                  ·
                    refine ⟨906378250653944760782161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1208504334205259681042881 906378250653944760782161)
                    ·
                      refine ⟨679783687990458570586621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906378250653944760782161 679783687990458570586621)
                      ·
                        rfl

theorem cell23_1323874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1323874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323874 prefixEnd_1323874 := by exact prefixLift 1323874
  have htrace : WordTrace (prefixWord ++ tailWord_1323874) baseStart_1323874 baseEnd_1323874 := by
    simpa [prefixWord, tailWord_1323874, baseEnd_1323874] using wordTrace_append hprefix tailTrace_1323874
  have hstable : (prefixWord ++ tailWord_1323874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323874).length < 2 ^ (prefixWord ++ tailWord_1323874).sum := by decide
  have hdescent : baseEnd_1323874 < baseStart_1323874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323896 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 6, 2]
def baseStart_1323896 : Nat := 118140960795 + 1323896 * 2 ^ 59
def prefixEnd_1323896 : Nat := 4983230072969 + 3 ^ 40 * 1323896 * 2
def baseEnd_1323896 : Nat := 679794984564857484511519

theorem tailTrace_1323896 : CollatzResearch.WordTrace tailWord_1323896 prefixEnd_1323896 679794984564857484511519 := by
  unfold tailWord_1323896
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143227005879185140447771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32190969341172246853930361 24143227005879185140447771)
  ·
    refine ⟨36214840508818777710671657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24143227005879185140447771 36214840508818777710671657)
    ·
      refine ⟨27161130381614083283003743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36214840508818777710671657 27161130381614083283003743)
      ·
        refine ⟨40741695572421124924505615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27161130381614083283003743 40741695572421124924505615)
        ·
          refine ⟨61112543358631687386758423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40741695572421124924505615 61112543358631687386758423)
          ·
            refine ⟨91668815037947531080137635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61112543358631687386758423 91668815037947531080137635)
            ·
              refine ⟨137503222556921296620206453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91668815037947531080137635 137503222556921296620206453)
              ·
                refine ⟨12890927114711371558144355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137503222556921296620206453 12890927114711371558144355)
                ·
                  refine ⟨19336390672067057337216533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12890927114711371558144355 19336390672067057337216533)
                  ·
                    refine ⟨906393312753143312682025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19336390672067057337216533 906393312753143312682025)
                    ·
                      refine ⟨679794984564857484511519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906393312753143312682025 679794984564857484511519)
                      ·
                        rfl

theorem cell23_1323896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_1323896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323896 prefixEnd_1323896 := by exact prefixLift 1323896
  have htrace : WordTrace (prefixWord ++ tailWord_1323896) baseStart_1323896 baseEnd_1323896 := by
    simpa [prefixWord, tailWord_1323896, baseEnd_1323896] using wordTrace_append hprefix tailTrace_1323896
  have hstable : (prefixWord ++ tailWord_1323896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323896).length < 2 ^ (prefixWord ++ tailWord_1323896).sum := by decide
  have hdescent : baseEnd_1323896 < baseStart_1323896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323916 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1323916 : Nat := 118140960795 + 1323916 * 2 ^ 59
def prefixEnd_1323916 : Nat := 4983230072969 + 3 ^ 40 * 1323916 * 2
def baseEnd_1323916 : Nat := 679805254177947406261427

theorem tailTrace_1323916 : CollatzResearch.WordTrace tailWord_1323916 prefixEnd_1323916 679805254177947406261427 := by
  unfold tailWord_1323916
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143591735842956848311801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32191455647790609131082401 24143591735842956848311801)
  ·
    refine ⟨18107693801882217636233851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24143591735842956848311801 18107693801882217636233851)
    ·
      refine ⟨27161540702823326454350777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18107693801882217636233851 27161540702823326454350777)
      ·
        refine ⟨20371155527117494840763083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27161540702823326454350777 20371155527117494840763083)
        ·
          refine ⟨30556733290676242261144625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20371155527117494840763083 30556733290676242261144625)
          ·
            refine ⟨22917549968007181695858469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30556733290676242261144625 22917549968007181695858469)
            ·
              refine ⟨4297040619001346567973463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22917549968007181695858469 4297040619001346567973463)
              ·
                refine ⟨6445560928502019851960195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297040619001346567973463 6445560928502019851960195)
                ·
                  refine ⟨9668341392753029777940293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445560928502019851960195 9668341392753029777940293)
                  ·
                    refine ⟨1812814011141193083363805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9668341392753029777940293 1812814011141193083363805)
                    ·
                      refine ⟨679805254177947406261427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812814011141193083363805 679805254177947406261427)
                      ·
                        rfl

theorem cell23_1323916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1323916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323916 prefixEnd_1323916 := by exact prefixLift 1323916
  have htrace : WordTrace (prefixWord ++ tailWord_1323916) baseStart_1323916 baseEnd_1323916 := by
    simpa [prefixWord, tailWord_1323916, baseEnd_1323916] using wordTrace_append hprefix tailTrace_1323916
  have hstable : (prefixWord ++ tailWord_1323916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323916).length < 2 ^ (prefixWord ++ tailWord_1323916).sum := by decide
  have hdescent : baseEnd_1323916 < baseStart_1323916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323923 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 1, 4]
def baseStart_1323923 : Nat := 118140960795 + 1323923 * 2 ^ 59
def prefixEnd_1323923 : Nat := 4983230072969 + 3 ^ 40 * 1323923 * 2
def baseEnd_1323923 : Nat := 226602949514176292957965

theorem tailTrace_1323923 : CollatzResearch.WordTrace tailWord_1323923 prefixEnd_1323923 226602949514176292957965 := by
  unfold tailWord_1323923
  simp only [CollatzResearch.WordTrace]
  refine ⟨48287438782660553892128423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32191625855107035928085615 48287438782660553892128423)
  ·
    refine ⟨72431158173990830838192635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48287438782660553892128423 72431158173990830838192635)
    ·
      refine ⟨108646737260986246257288953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72431158173990830838192635 108646737260986246257288953)
      ·
        refine ⟨81485052945739684692966715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108646737260986246257288953 81485052945739684692966715)
        ·
          refine ⟨122227579418609527039450073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81485052945739684692966715 122227579418609527039450073)
          ·
            refine ⟨91670684563957145279587555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122227579418609527039450073 91670684563957145279587555)
            ·
              refine ⟨137506026845935717919381333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91670684563957145279587555 137506026845935717919381333)
              ·
                refine ⟨805699376050404597183875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 137506026845935717919381333 805699376050404597183875)
                ·
                  refine ⟨1208549064075606895775813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805699376050404597183875 1208549064075606895775813)
                  ·
                    refine ⟨226602949514176292957965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208549064075606895775813 226602949514176292957965)
                    ·
                      rfl

theorem cell23_1323923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 4].length) (baseStart_1323923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323923 prefixEnd_1323923 := by exact prefixLift 1323923
  have htrace : WordTrace (prefixWord ++ tailWord_1323923) baseStart_1323923 baseEnd_1323923 := by
    simpa [prefixWord, tailWord_1323923, baseEnd_1323923] using wordTrace_append hprefix tailTrace_1323923
  have hstable : (prefixWord ++ tailWord_1323923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323923).length < 2 ^ (prefixWord ++ tailWord_1323923).sum := by decide
  have hdescent : baseEnd_1323923 < baseStart_1323923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323933 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1323933 : Nat := 118140960795 + 1323933 * 2 ^ 59
def prefixEnd_1323933 : Nat := 4983230072969 + 3 ^ 40 * 1323933 * 2
def baseEnd_1323933 : Nat := 679813983349073839748849

theorem tailTrace_1323933 : CollatzResearch.WordTrace tailWord_1323933 prefixEnd_1323933 679813983349073839748849 := by
  unfold tailWord_1323933
  simp only [CollatzResearch.WordTrace]
  refine ⟨48287803512624325599992453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32191869008416217066661635 48287803512624325599992453)
  ·
    refine ⟨9053963158617061049998585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48287803512624325599992453 9053963158617061049998585)
    ·
      refine ⟨6790472368962795787498939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9053963158617061049998585 6790472368962795787498939)
      ·
        refine ⟨10185708553444193681248409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790472368962795787498939 10185708553444193681248409)
        ·
          refine ⟨7639281415083145260936307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10185708553444193681248409 7639281415083145260936307)
          ·
            refine ⟨11458922122624717891404461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7639281415083145260936307 11458922122624717891404461)
            ·
              refine ⟨4297095795984269209276673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11458922122624717891404461 4297095795984269209276673)
              ·
                refine ⟨3222821846988201906957505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297095795984269209276673 3222821846988201906957505)
                ·
                  refine ⟨2417116385241151430218129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3222821846988201906957505 2417116385241151430218129)
                  ·
                    refine ⟨1812837288930863572663597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2417116385241151430218129 1812837288930863572663597)
                    ·
                      refine ⟨679813983349073839748849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812837288930863572663597 679813983349073839748849)
                      ·
                        rfl

theorem cell23_1323933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1323933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323933 prefixEnd_1323933 := by exact prefixLift 1323933
  have htrace : WordTrace (prefixWord ++ tailWord_1323933) baseStart_1323933 baseEnd_1323933 := by
    simpa [prefixWord, tailWord_1323933, baseEnd_1323933] using wordTrace_append hprefix tailTrace_1323933
  have hstable : (prefixWord ++ tailWord_1323933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323933).length < 2 ^ (prefixWord ++ tailWord_1323933).sum := by decide
  have hdescent : baseEnd_1323933 < baseStart_1323933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323939 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1323939 : Nat := 118140960795 + 1323939 * 2 ^ 59
def prefixEnd_1323939 : Nat := 4983230072969 + 3 ^ 40 * 1323939 * 2
def baseEnd_1323939 : Nat := 679817064233000816273821

theorem tailTrace_1323939 : CollatzResearch.WordTrace tailWord_1323939 prefixEnd_1323939 679817064233000816273821 := by
  unfold tailWord_1323939
  simp only [CollatzResearch.WordTrace]
  refine ⟨48288022350602588624710871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32192014900401725749807247 48288022350602588624710871)
  ·
    refine ⟨72432033525903882937066307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48288022350602588624710871 72432033525903882937066307)
    ·
      refine ⟨108648050288855824405599461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72432033525903882937066307 108648050288855824405599461)
      ·
        refine ⟨20371509429160467076049899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108648050288855824405599461 20371509429160467076049899)
        ·
          refine ⟨30557264143740700614074849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20371509429160467076049899 30557264143740700614074849)
          ·
            refine ⟨22917948107805525460556137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30557264143740700614074849 22917948107805525460556137)
            ·
              refine ⟨17188461080854144095417103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22917948107805525460556137 17188461080854144095417103)
              ·
                refine ⟨25782691621281216143125655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17188461080854144095417103 25782691621281216143125655)
                ·
                  refine ⟨38674037431921824214688483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25782691621281216143125655 38674037431921824214688483)
                  ·
                    refine ⟨58011056147882736322032725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38674037431921824214688483 58011056147882736322032725)
                    ·
                      refine ⟨679817064233000816273821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58011056147882736322032725 679817064233000816273821)
                      ·
                        rfl

theorem cell23_1323939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1323939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323939 prefixEnd_1323939 := by exact prefixLift 1323939
  have htrace : WordTrace (prefixWord ++ tailWord_1323939) baseStart_1323939 baseEnd_1323939 := by
    simpa [prefixWord, tailWord_1323939, baseEnd_1323939] using wordTrace_append hprefix tailTrace_1323939
  have hstable : (prefixWord ++ tailWord_1323939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323939).length < 2 ^ (prefixWord ++ tailWord_1323939).sum := by decide
  have hdescent : baseEnd_1323939 < baseStart_1323939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323953 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 6]
def baseStart_1323953 : Nat := 118140960795 + 1323953 * 2 ^ 59
def prefixEnd_1323953 : Nat := 4983230072969 + 3 ^ 40 * 1323953 * 2
def baseEnd_1323953 : Nat := 75536028106907084610973

theorem tailTrace_1323953 : CollatzResearch.WordTrace tailWord_1323953 prefixEnd_1323953 75536028106907084610973 := by
  unfold tailWord_1323953
  simp only [CollatzResearch.WordTrace]
  refine ⟨48288532972551869015720513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32192355315034579343813675 48288532972551869015720513)
  ·
    refine ⟨36216399729413901761790385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48288532972551869015720513 36216399729413901761790385)
    ·
      refine ⟨27162299797060426321342789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36216399729413901761790385 27162299797060426321342789)
      ·
        refine ⟨5092931211948829935251773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27162299797060426321342789 5092931211948829935251773)
        ·
          refine ⟨1909849204480811225719415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5092931211948829935251773 1909849204480811225719415)
          ·
            refine ⟨2864773806721216838579123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909849204480811225719415 2864773806721216838579123)
            ·
              refine ⟨4297160710081825257868685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864773806721216838579123 4297160710081825257868685)
              ·
                refine ⟨1611435266280684471700757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4297160710081825257868685 1611435266280684471700757)
                ·
                  refine ⟨75536028106907084610973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1611435266280684471700757 75536028106907084610973)
                  ·
                    rfl

theorem cell23_1323953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 6].length) (baseStart_1323953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1323953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1323953 prefixEnd_1323953 := by exact prefixLift 1323953
  have htrace : WordTrace (prefixWord ++ tailWord_1323953) baseStart_1323953 baseEnd_1323953 := by
    simpa [prefixWord, tailWord_1323953, baseEnd_1323953] using wordTrace_append hprefix tailTrace_1323953
  have hstable : (prefixWord ++ tailWord_1323953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323953).length < 2 ^ (prefixWord ++ tailWord_1323953).sum := by decide
  have hdescent : baseEnd_1323953 < baseStart_1323953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324033 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1324033 : Nat := 118140960795 + 1324033 * 2 ^ 59
def prefixEnd_1324033 : Nat := 4983230072969 + 3 ^ 40 * 1324033 * 2
def baseEnd_1324033 : Nat := 679865331414523448498389

theorem tailTrace_1324033 : CollatzResearch.WordTrace tailWord_1324033 prefixEnd_1324033 679865331414523448498389 := by
  unfold tailWord_1324033
  simp only [CollatzResearch.WordTrace]
  refine ⟨48291450812262042678632753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32194300541508028452421835 48291450812262042678632753)
  ·
    refine ⟨36218588109196532008974565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48291450812262042678632753 36218588109196532008974565)
    ·
      refine ⟨6790985270474349751682731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36218588109196532008974565 6790985270474349751682731)
      ·
        refine ⟨10186477905711524627524097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790985270474349751682731 10186477905711524627524097)
        ·
          refine ⟨7639858429283643470643073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10186477905711524627524097 7639858429283643470643073)
          ·
            refine ⟨5729893821962732602982305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7639858429283643470643073 5729893821962732602982305)
            ·
              refine ⟨4297420366472049452236729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5729893821962732602982305 4297420366472049452236729)
              ·
                refine ⟨3223065274854037089177547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297420366472049452236729 3223065274854037089177547)
                ·
                  refine ⟨4834597912281055633766321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223065274854037089177547 4834597912281055633766321)
                  ·
                    refine ⟨3625948434210791725324741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4834597912281055633766321 3625948434210791725324741)
                    ·
                      refine ⟨679865331414523448498389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3625948434210791725324741 679865331414523448498389)
                      ·
                        rfl

theorem cell23_1324033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1324033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324033 prefixEnd_1324033 := by exact prefixLift 1324033
  have htrace : WordTrace (prefixWord ++ tailWord_1324033) baseStart_1324033 baseEnd_1324033 := by
    simpa [prefixWord, tailWord_1324033, baseEnd_1324033] using wordTrace_append hprefix tailTrace_1324033
  have hstable : (prefixWord ++ tailWord_1324033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324033).length < 2 ^ (prefixWord ++ tailWord_1324033).sum := by decide
  have hdescent : baseEnd_1324033 < baseStart_1324033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324040 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_1324040 : Nat := 118140960795 + 1324040 * 2 ^ 59
def prefixEnd_1324040 : Nat := 4983230072969 + 3 ^ 40 * 1324040 * 2
def baseEnd_1324040 : Nat := 679868925779104921110857

theorem tailTrace_1324040 : CollatzResearch.WordTrace tailWord_1324040 prefixEnd_1324040 679868925779104921110857 := by
  unfold tailWord_1324040
  simp only [CollatzResearch.WordTrace]
  refine ⟨24145853061618341437068787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32194470748824455249425049 24145853061618341437068787)
  ·
    refine ⟨36218779592427512155603181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24145853061618341437068787 36218779592427512155603181)
    ·
      refine ⟨13582042347160317058351193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36218779592427512155603181 13582042347160317058351193)
      ·
        refine ⟨10186531760370237793763395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13582042347160317058351193 10186531760370237793763395)
        ·
          refine ⟨15279797640555356690645093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10186531760370237793763395 15279797640555356690645093)
          ·
            refine ⟨2864962057604129379495955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15279797640555356690645093 2864962057604129379495955)
            ·
              refine ⟨4297443086406194069243933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864962057604129379495955 4297443086406194069243933)
              ·
                refine ⟨1611541157402322775966475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4297443086406194069243933 1611541157402322775966475)
                ·
                  refine ⟨2417311736103484163949713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611541157402322775966475 2417311736103484163949713)
                  ·
                    refine ⟨1812983802077613122962285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2417311736103484163949713 1812983802077613122962285)
                    ·
                      refine ⟨679868925779104921110857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1812983802077613122962285 679868925779104921110857)
                      ·
                        rfl

theorem cell23_1324040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_1324040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324040 prefixEnd_1324040 := by exact prefixLift 1324040
  have htrace : WordTrace (prefixWord ++ tailWord_1324040) baseStart_1324040 baseEnd_1324040 := by
    simpa [prefixWord, tailWord_1324040, baseEnd_1324040] using wordTrace_append hprefix tailTrace_1324040
  have hstable : (prefixWord ++ tailWord_1324040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324040).length < 2 ^ (prefixWord ++ tailWord_1324040).sum := by decide
  have hdescent : baseEnd_1324040 < baseStart_1324040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324064 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 2, 4]
def baseStart_1324064 : Nat := 118140960795 + 1324064 * 2 ^ 59
def prefixEnd_1324064 : Nat := 4983230072969 + 3 ^ 40 * 1324064 * 2
def baseEnd_1324064 : Nat := 226627083104937609070249

theorem tailTrace_1324064 : CollatzResearch.WordTrace tailWord_1324064 prefixEnd_1324064 226627083104937609070249 := by
  unfold tailWord_1324064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24146290737574867486505623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32195054316766489982007497 24146290737574867486505623)
  ·
    refine ⟨36219436106362301229758435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24146290737574867486505623 36219436106362301229758435)
    ·
      refine ⟨54329154159543451844637653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36219436106362301229758435 54329154159543451844637653)
      ·
        refine ⟨1273339550614299652608695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 54329154159543451844637653 1273339550614299652608695)
        ·
          refine ⟨1910009325921449478913043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273339550614299652608695 1910009325921449478913043)
          ·
            refine ⟨2865013988882174218369565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910009325921449478913043 2865013988882174218369565)
            ·
              refine ⟨1074380245830815331888587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2865013988882174218369565 1074380245830815331888587)
              ·
                refine ⟨1611570368746222997832881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074380245830815331888587 1611570368746222997832881)
                ·
                  refine ⟨1208677776559667248374661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1611570368746222997832881 1208677776559667248374661)
                  ·
                    refine ⟨226627083104937609070249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208677776559667248374661 226627083104937609070249)
                    ·
                      rfl

theorem cell23_1324064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 4].length) (baseStart_1324064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324064 prefixEnd_1324064 := by exact prefixLift 1324064
  have htrace : WordTrace (prefixWord ++ tailWord_1324064) baseStart_1324064 baseEnd_1324064 := by
    simpa [prefixWord, tailWord_1324064, baseEnd_1324064] using wordTrace_append hprefix tailTrace_1324064
  have hstable : (prefixWord ++ tailWord_1324064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324064).length < 2 ^ (prefixWord ++ tailWord_1324064).sum := by decide
  have hdescent : baseEnd_1324064 < baseStart_1324064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324127 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 2, 2, 2]
def baseStart_1324127 : Nat := 118140960795 + 1324127 * 2 ^ 59
def prefixEnd_1324127 : Nat := 4983230072969 + 3 ^ 40 * 1324127 * 2
def baseEnd_1324127 : Nat := 679913598596046080722957

theorem tailTrace_1324127 : CollatzResearch.WordTrace tailWord_1324127 prefixEnd_1324127 679913598596046080722957 := by
  unfold tailWord_1324127
  simp only [CollatzResearch.WordTrace]
  refine ⟨48294879273921496732554635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32196586182614331155036423 48294879273921496732554635)
  ·
    refine ⟨72442318910882245098831953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48294879273921496732554635 72442318910882245098831953)
    ·
      refine ⟨54331739183161683824123965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72442318910882245098831953 54331739183161683824123965)
      ·
        refine ⟨20374402193685631434046487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54331739183161683824123965 20374402193685631434046487)
        ·
          refine ⟨30561603290528447151069731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20374402193685631434046487 30561603290528447151069731)
          ·
            refine ⟨45842404935792670726604597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30561603290528447151069731 45842404935792670726604597)
            ·
              refine ⟨4297725462730562880619181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45842404935792670726604597 4297725462730562880619181)
              ·
                refine ⟨1611647048523961080232193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4297725462730562880619181 1611647048523961080232193)
                ·
                  refine ⟨1208735286392970810174145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1611647048523961080232193 1208735286392970810174145)
                  ·
                    refine ⟨906551464794728107630609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1208735286392970810174145 906551464794728107630609)
                    ·
                      refine ⟨679913598596046080722957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906551464794728107630609 679913598596046080722957)
                      ·
                        rfl

theorem cell23_1324127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_1324127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324127 prefixEnd_1324127 := by exact prefixLift 1324127
  have htrace : WordTrace (prefixWord ++ tailWord_1324127) baseStart_1324127 baseEnd_1324127 := by
    simpa [prefixWord, tailWord_1324127, baseEnd_1324127] using wordTrace_append hprefix tailTrace_1324127
  have hstable : (prefixWord ++ tailWord_1324127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324127).length < 2 ^ (prefixWord ++ tailWord_1324127).sum := by decide
  have hdescent : baseEnd_1324127 < baseStart_1324127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324130 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1324130 : Nat := 118140960795 + 1324130 * 2 ^ 59
def prefixEnd_1324130 : Nat := 4983230072969 + 3 ^ 40 * 1324130 * 2
def baseEnd_1324130 : Nat := 679915139038009568985443

theorem tailTrace_1324130 : CollatzResearch.WordTrace tailWord_1324130 prefixEnd_1324130 679915139038009568985443 := by
  unfold tailWord_1324130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073747173227657061228461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32196659128607085496609229 12073747173227657061228461)
  ·
    refine ⟨4527655189960371397960673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12073747173227657061228461 4527655189960371397960673)
    ·
      refine ⟨3395741392470278548470505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4527655189960371397960673 3395741392470278548470505)
      ·
        refine ⟨2546806044352708911352879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3395741392470278548470505 2546806044352708911352879)
        ·
          refine ⟨3820209066529063367029319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546806044352708911352879 3820209066529063367029319)
          ·
            refine ⟨5730313599793595050543979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820209066529063367029319 5730313599793595050543979)
            ·
              refine ⟨8595470399690392575815969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5730313599793595050543979 8595470399690392575815969)
              ·
                refine ⟨6446602799767794431861977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8595470399690392575815969 6446602799767794431861977)
                ·
                  refine ⟨4834952099825845823896483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6446602799767794431861977 4834952099825845823896483)
                  ·
                    refine ⟨7252428149738768735844725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4834952099825845823896483 7252428149738768735844725)
                    ·
                      refine ⟨679915139038009568985443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7252428149738768735844725 679915139038009568985443)
                      ·
                        rfl

theorem cell23_1324130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1324130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324130 prefixEnd_1324130 := by exact prefixLift 1324130
  have htrace : WordTrace (prefixWord ++ tailWord_1324130) baseStart_1324130 baseEnd_1324130 := by
    simpa [prefixWord, tailWord_1324130, baseEnd_1324130] using wordTrace_append hprefix tailTrace_1324130
  have hstable : (prefixWord ++ tailWord_1324130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324130).length < 2 ^ (prefixWord ++ tailWord_1324130).sum := by decide
  have hdescent : baseEnd_1324130 < baseStart_1324130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324163 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 2, 5]
def baseStart_1324163 : Nat := 118140960795 + 1324163 * 2 ^ 59
def prefixEnd_1324163 : Nat := 4983230072969 + 3 ^ 40 * 1324163 * 2
def baseEnd_1324163 : Nat := 226644027966535979957597

theorem tailTrace_1324163 : CollatzResearch.WordTrace tailWord_1324163 prefixEnd_1324163 226644027966535979957597 := by
  unfold tailWord_1324163
  simp only [CollatzResearch.WordTrace]
  refine ⟨48296192301791074880865143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32197461534527383253910095 48296192301791074880865143)
  ·
    refine ⟨72444288452686612321297715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48296192301791074880865143 72444288452686612321297715)
    ·
      refine ⟨108666432679029918481946573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72444288452686612321297715 108666432679029918481946573)
      ·
        refine ⟨40749912254636219430729965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108666432679029918481946573 40749912254636219430729965)
        ·
          refine ⟨15281217095488582286523737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40749912254636219430729965 15281217095488582286523737)
          ·
            refine ⟨11460912821616436714892803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15281217095488582286523737 11460912821616436714892803)
            ·
              refine ⟨17191369232424655072339205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11460912821616436714892803 17191369232424655072339205)
              ·
                refine ⟨3223381731079622826063601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17191369232424655072339205 3223381731079622826063601)
                ·
                  refine ⟨2417536298309717119547701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223381731079622826063601 2417536298309717119547701)
                  ·
                    refine ⟨226644027966535979957597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2417536298309717119547701 226644027966535979957597)
                    ·
                      rfl

theorem cell23_1324163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 5].length) (baseStart_1324163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324163 prefixEnd_1324163 := by exact prefixLift 1324163
  have htrace : WordTrace (prefixWord ++ tailWord_1324163) baseStart_1324163 baseEnd_1324163 := by
    simpa [prefixWord, tailWord_1324163, baseEnd_1324163] using wordTrace_append hprefix tailTrace_1324163
  have hstable : (prefixWord ++ tailWord_1324163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324163).length < 2 ^ (prefixWord ++ tailWord_1324163).sum := by decide
  have hdescent : baseEnd_1324163 < baseStart_1324163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324170 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_1324170 : Nat := 118140960795 + 1324170 * 2 ^ 59
def prefixEnd_1324170 : Nat := 4983230072969 + 3 ^ 40 * 1324170 * 2
def baseEnd_1324170 : Nat := 679935678264189412485259

theorem tailTrace_1324170 : CollatzResearch.WordTrace tailWord_1324170 prefixEnd_1324170 679935678264189412485259 := by
  unfold tailWord_1324170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12074111903191428769092491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32197631741843810050913309 12074111903191428769092491)
  ·
    refine ⟨18111167854787143153638737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12074111903191428769092491 18111167854787143153638737)
    ·
      refine ⟨13583375891090357365229053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18111167854787143153638737 13583375891090357365229053)
      ·
        refine ⟨5093765959158884011960895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13583375891090357365229053 5093765959158884011960895)
        ·
          refine ⟨7640648938738326017941343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5093765959158884011960895 7640648938738326017941343)
          ·
            refine ⟨11460973408107489026912015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7640648938738326017941343 11460973408107489026912015)
            ·
              refine ⟨17191460112161233540368023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11460973408107489026912015 17191460112161233540368023)
              ·
                refine ⟨25787190168241850310552035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17191460112161233540368023 25787190168241850310552035)
                ·
                  refine ⟨38680785252362775465828053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25787190168241850310552035 38680785252362775465828053)
                  ·
                    refine ⟨906580904352252549980345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38680785252362775465828053 906580904352252549980345)
                    ·
                      refine ⟨679935678264189412485259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906580904352252549980345 679935678264189412485259)
                      ·
                        rfl

theorem cell23_1324170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_1324170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324170 prefixEnd_1324170 := by exact prefixLift 1324170
  have htrace : WordTrace (prefixWord ++ tailWord_1324170) baseStart_1324170 baseEnd_1324170 := by
    simpa [prefixWord, tailWord_1324170, baseEnd_1324170] using wordTrace_append hprefix tailTrace_1324170
  have hstable : (prefixWord ++ tailWord_1324170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324170).length < 2 ^ (prefixWord ++ tailWord_1324170).sum := by decide
  have hdescent : baseEnd_1324170 < baseStart_1324170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324261 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_1324261 : Nat := 118140960795 + 1324261 * 2 ^ 59
def prefixEnd_1324261 : Nat := 4983230072969 + 3 ^ 40 * 1324261 * 2
def baseEnd_1324261 : Nat := 226660801667916185482447

theorem tailTrace_1324261 : CollatzResearch.WordTrace tailWord_1324261 prefixEnd_1324261 226660801667916185482447 := by
  unfold tailWord_1324261
  simp only [CollatzResearch.WordTrace]
  refine ⟨48299766655436037617932637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32199844436957358411955091 48299766655436037617932637)
  ·
    refine ⟨18112412495788514106724739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48299766655436037617932637 18112412495788514106724739)
    ·
      refine ⟨27168618743682771160087109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18112412495788514106724739 27168618743682771160087109)
      ·
        refine ⟨5094116014440519592516333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27168618743682771160087109 5094116014440519592516333)
        ·
          refine ⟨1910293505415194847193625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5094116014440519592516333 1910293505415194847193625)
          ·
            refine ⟨1432720129061396135395219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910293505415194847193625 1432720129061396135395219)
            ·
              refine ⟨2149080193592094203092829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432720129061396135395219 2149080193592094203092829)
              ·
                refine ⟨805905072597035326159811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149080193592094203092829 805905072597035326159811)
                ·
                  refine ⟨1208857608895552989239717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805905072597035326159811 1208857608895552989239717)
                  ·
                    refine ⟨226660801667916185482447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208857608895552989239717 226660801667916185482447)
                    ·
                      rfl

theorem cell23_1324261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_1324261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324261 prefixEnd_1324261 := by exact prefixLift 1324261
  have htrace : WordTrace (prefixWord ++ tailWord_1324261) baseStart_1324261 baseEnd_1324261 := by
    simpa [prefixWord, tailWord_1324261, baseEnd_1324261] using wordTrace_append hprefix tailTrace_1324261
  have hstable : (prefixWord ++ tailWord_1324261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324261).length < 2 ^ (prefixWord ++ tailWord_1324261).sum := by decide
  have hdescent : baseEnd_1324261 < baseStart_1324261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324317 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1324317 : Nat := 118140960795 + 1324317 * 2 ^ 59
def prefixEnd_1324317 : Nat := 4983230072969 + 3 ^ 40 * 1324317 * 2
def baseEnd_1324317 : Nat := 226670386640133445782361

theorem tailTrace_1324317 : CollatzResearch.WordTrace tailWord_1324317 prefixEnd_1324317 226670386640133445782361 := by
  unfold tailWord_1324317
  simp only [CollatzResearch.WordTrace]
  refine ⟨48301809143233159181971205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32201206095488772787980803 48301809143233159181971205)
  ·
    refine ⟨9056589214356217346619601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48301809143233159181971205 9056589214356217346619601)
    ·
      refine ⟨6792441910767163009964701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9056589214356217346619601 6792441910767163009964701)
      ·
        refine ⟨2547165716537686128736763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6792441910767163009964701 2547165716537686128736763)
        ·
          refine ⟨3820748574806529193105145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547165716537686128736763 3820748574806529193105145)
          ·
            refine ⟨2865561431104896894828859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3820748574806529193105145 2865561431104896894828859)
            ·
              refine ⟨4298342146657345342243289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865561431104896894828859 4298342146657345342243289)
              ·
                refine ⟨3223756609993009006682467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4298342146657345342243289 3223756609993009006682467)
                ·
                  refine ⟨4835634914989513510023701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223756609993009006682467 4835634914989513510023701)
                  ·
                    refine ⟨226670386640133445782361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4835634914989513510023701 226670386640133445782361)
                    ·
                      rfl

theorem cell23_1324317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1324317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324317 prefixEnd_1324317 := by exact prefixLift 1324317
  have htrace : WordTrace (prefixWord ++ tailWord_1324317) baseStart_1324317 baseEnd_1324317 := by
    simpa [prefixWord, tailWord_1324317, baseEnd_1324317] using wordTrace_append hprefix tailTrace_1324317
  have hstable : (prefixWord ++ tailWord_1324317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324317).length < 2 ^ (prefixWord ++ tailWord_1324317).sum := by decide
  have hdescent : baseEnd_1324317 < baseStart_1324317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324324 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_1324324 : Nat := 118140960795 + 1324324 * 2 ^ 59
def prefixEnd_1324324 : Nat := 4983230072969 + 3 ^ 40 * 1324324 * 2
def baseEnd_1324324 : Nat := 680014754284981809959551

theorem tailTrace_1324324 : CollatzResearch.WordTrace tailWord_1324324 prefixEnd_1324324 680014754284981809959551 := by
  unfold tailWord_1324324
  simp only [CollatzResearch.WordTrace]
  refine ⟨24151032227103899688738013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32201376302805199584984017 24151032227103899688738013)
  ·
    refine ⟨9056637085163962383276755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24151032227103899688738013 9056637085163962383276755)
    ·
      refine ⟨13584955627745943574915133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9056637085163962383276755 13584955627745943574915133)
      ·
        refine ⟨5094358360404728840593175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13584955627745943574915133 5094358360404728840593175)
        ·
          refine ⟨7641537540607093260889763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5094358360404728840593175 7641537540607093260889763)
          ·
            refine ⟨11462306310910639891334645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7641537540607093260889763 11462306310910639891334645)
            ·
              refine ⟨1074591216647872489812623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11462306310910639891334645 1074591216647872489812623)
              ·
                refine ⟨1611886824971808734718935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074591216647872489812623 1611886824971808734718935)
                ·
                  refine ⟨2417830237457713102078403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611886824971808734718935 2417830237457713102078403)
                  ·
                    refine ⟨3626745356186569653117605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2417830237457713102078403 3626745356186569653117605)
                    ·
                      refine ⟨680014754284981809959551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3626745356186569653117605 680014754284981809959551)
                      ·
                        rfl

theorem cell23_1324324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_1324324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324324 prefixEnd_1324324 := by exact prefixLift 1324324
  have htrace : WordTrace (prefixWord ++ tailWord_1324324) baseStart_1324324 baseEnd_1324324 := by
    simpa [prefixWord, tailWord_1324324, baseEnd_1324324] using wordTrace_append hprefix tailTrace_1324324
  have hstable : (prefixWord ++ tailWord_1324324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324324).length < 2 ^ (prefixWord ++ tailWord_1324324).sum := by decide
  have hdescent : baseEnd_1324324 < baseStart_1324324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324330 : List Nat := [3, 1, 4, 2, 1, 12]
def baseStart_1324330 : Nat := 118140960795 + 1324330 * 2 ^ 59
def prefixEnd_1324330 : Nat := 4983230072969 + 3 ^ 40 * 1324330 * 2
def baseEnd_1324330 : Nat := 2798427305221846857961

theorem tailTrace_1324330 : CollatzResearch.WordTrace tailWord_1324330 prefixEnd_1324330 2798427305221846857961 := by
  unfold tailWord_1324330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12075570823046515600548611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32201522194790708268129629 12075570823046515600548611)
  ·
    refine ⟨18113356234569773400822917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12075570823046515600548611 18113356234569773400822917)
    ·
      refine ⟨3396254293981832512654297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18113356234569773400822917 3396254293981832512654297)
      ·
        refine ⟨2547190720486374384490723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3396254293981832512654297 2547190720486374384490723)
        ·
          refine ⟨3820786080729561576736085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547190720486374384490723 3820786080729561576736085)
          ·
            refine ⟨2798427305221846857961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3820786080729561576736085 2798427305221846857961)
            ·
              rfl

theorem cell23_1324330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 12].length) (baseStart_1324330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324330 prefixEnd_1324330 := by exact prefixLift 1324330
  have htrace : WordTrace (prefixWord ++ tailWord_1324330) baseStart_1324330 baseEnd_1324330 := by
    simpa [prefixWord, tailWord_1324330, baseEnd_1324330] using wordTrace_append hprefix tailTrace_1324330
  have hstable : (prefixWord ++ tailWord_1324330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324330).length < 2 ^ (prefixWord ++ tailWord_1324330).sum := by decide
  have hdescent : baseEnd_1324330 < baseStart_1324330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324370 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1324370 : Nat := 118140960795 + 1324370 * 2 ^ 59
def prefixEnd_1324370 : Nat := 4983230072969 + 3 ^ 40 * 1324370 * 2
def baseEnd_1324370 : Nat := 680038374395088629984339

theorem tailTrace_1324370 : CollatzResearch.WordTrace tailWord_1324370 prefixEnd_1324370 680038374395088629984339 := by
  unfold tailWord_1324370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12075935553010287308412641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32202494808027432822433709 12075935553010287308412641)
  ·
    refine ⟨9056951664757715481309481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12075935553010287308412641 9056951664757715481309481)
    ·
      refine ⟨6792713748568286610982111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9056951664757715481309481 6792713748568286610982111)
      ·
        refine ⟨10189070622852429916473167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6792713748568286610982111 10189070622852429916473167)
        ·
          refine ⟨15283605934278644874709751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10189070622852429916473167 15283605934278644874709751)
          ·
            refine ⟨22925408901417967312064627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15283605934278644874709751 22925408901417967312064627)
            ·
              refine ⟨34388113352126950968096941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22925408901417967312064627 34388113352126950968096941)
              ·
                refine ⟨12895542507047606613036353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34388113352126950968096941 12895542507047606613036353)
                ·
                  refine ⟨9671656880285704959777265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12895542507047606613036353 9671656880285704959777265)
                  ·
                    refine ⟨7253742660214278719832949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9671656880285704959777265 7253742660214278719832949)
                    ·
                      refine ⟨680038374395088629984339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7253742660214278719832949 680038374395088629984339)
                      ·
                        rfl

theorem cell23_1324370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1324370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324370 prefixEnd_1324370 := by exact prefixLift 1324370
  have htrace : WordTrace (prefixWord ++ tailWord_1324370) baseStart_1324370 baseEnd_1324370 := by
    simpa [prefixWord, tailWord_1324370, baseEnd_1324370] using wordTrace_append hprefix tailTrace_1324370
  have hstable : (prefixWord ++ tailWord_1324370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324370).length < 2 ^ (prefixWord ++ tailWord_1324370).sum := by decide
  have hdescent : baseEnd_1324370 < baseStart_1324370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324418 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1324418 : Nat := 118140960795 + 1324418 * 2 ^ 59
def prefixEnd_1324418 : Nat := 4983230072969 + 3 ^ 40 * 1324418 * 2
def baseEnd_1324418 : Nat := 680063021466504442184119

theorem tailTrace_1324418 : CollatzResearch.WordTrace tailWord_1324418 prefixEnd_1324418 680063021466504442184119 := by
  unfold tailWord_1324418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076373228966813357849477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32203661943911502287598605 12076373228966813357849477)
  ·
    refine ⟨2264319980431277504596777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12076373228966813357849477 2264319980431277504596777)
    ·
      refine ⟨1698239985323458128447583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2264319980431277504596777 1698239985323458128447583)
      ·
        refine ⟨2547359977985187192671375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698239985323458128447583 2547359977985187192671375)
        ·
          refine ⟨3821039966977780789007063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547359977985187192671375 3821039966977780789007063)
          ·
            refine ⟨5731559950466671183510595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821039966977780789007063 5731559950466671183510595)
            ·
              refine ⟨8597339925700006775265893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731559950466671183510595 8597339925700006775265893)
              ·
                refine ⟨1612001236068751270362355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8597339925700006775265893 1612001236068751270362355)
                ·
                  refine ⟨2418001854103126905543533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612001236068751270362355 2418001854103126905543533)
                  ·
                    refine ⟨906750695288672589578825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418001854103126905543533 906750695288672589578825)
                    ·
                      refine ⟨680063021466504442184119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906750695288672589578825 680063021466504442184119)
                      ·
                        rfl

theorem cell23_1324418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1324418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324418 prefixEnd_1324418 := by exact prefixLift 1324418
  have htrace : WordTrace (prefixWord ++ tailWord_1324418) baseStart_1324418 baseEnd_1324418 := by
    simpa [prefixWord, tailWord_1324418, baseEnd_1324418] using wordTrace_append hprefix tailTrace_1324418
  have hstable : (prefixWord ++ tailWord_1324418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324418).length < 2 ^ (prefixWord ++ tailWord_1324418).sum := by decide
  have hdescent : baseEnd_1324418 < baseStart_1324418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324460 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_1324460 : Nat := 118140960795 + 1324460 * 2 ^ 59
def prefixEnd_1324460 : Nat := 4983230072969 + 3 ^ 40 * 1324460 * 2
def baseEnd_1324460 : Nat := 680084587653993277858925

theorem tailTrace_1324460 : CollatzResearch.WordTrace tailWord_1324460 prefixEnd_1324460 680084587653993277858925 := by
  unfold tailWord_1324460
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153512390857547302213417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32204683187810063069617889 24153512390857547302213417)
  ·
    refine ⟨18115134293143160476660063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24153512390857547302213417 18115134293143160476660063)
    ·
      refine ⟨27172701439714740714990095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18115134293143160476660063 27172701439714740714990095)
      ·
        refine ⟨40759052159572111072485143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27172701439714740714990095 40759052159572111072485143)
        ·
          refine ⟨61138578239358166608727715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40759052159572111072485143 61138578239358166608727715)
          ·
            refine ⟨91707867359037249913091573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61138578239358166608727715 91707867359037249913091573)
            ·
              refine ⟨8597612564909742179352335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91707867359037249913091573 8597612564909742179352335)
              ·
                refine ⟨12896418847364613269028503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8597612564909742179352335 12896418847364613269028503)
                ·
                  refine ⟨19344628271046919903542755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12896418847364613269028503 19344628271046919903542755)
                  ·
                    refine ⟨29016942406570379855314133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19344628271046919903542755 29016942406570379855314133)
                    ·
                      refine ⟨680084587653993277858925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29016942406570379855314133 680084587653993277858925)
                      ·
                        rfl

theorem cell23_1324460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_1324460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324460 prefixEnd_1324460 := by exact prefixLift 1324460
  have htrace : WordTrace (prefixWord ++ tailWord_1324460) baseStart_1324460 baseEnd_1324460 := by
    simpa [prefixWord, tailWord_1324460, baseEnd_1324460] using wordTrace_append hprefix tailTrace_1324460
  have hstable : (prefixWord ++ tailWord_1324460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324460).length < 2 ^ (prefixWord ++ tailWord_1324460).sum := by decide
  have hdescent : baseEnd_1324460 < baseStart_1324460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324480 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_1324480 : Nat := 118140960795 + 1324480 * 2 ^ 59
def prefixEnd_1324480 : Nat := 4983230072969 + 3 ^ 40 * 1324480 * 2
def baseEnd_1324480 : Nat := 226698285755694399869611

theorem tailTrace_1324480 : CollatzResearch.WordTrace tailWord_1324480 prefixEnd_1324480 226698285755694399869611 := by
  unfold tailWord_1324480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153877120821319010077447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32205169494428425346769929 24153877120821319010077447)
  ·
    refine ⟨36230815681231978515116171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24153877120821319010077447 36230815681231978515116171)
    ·
      refine ⟨54346223521847967772674257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36230815681231978515116171 54346223521847967772674257)
      ·
        refine ⟨40759667641385975829505693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54346223521847967772674257 40759667641385975829505693)
        ·
          refine ⟨15284875365519740936064635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40759667641385975829505693 15284875365519740936064635)
          ·
            refine ⟨22927313048279611404096953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15284875365519740936064635 22927313048279611404096953)
            ·
              refine ⟨17195484786209708553072715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22927313048279611404096953 17195484786209708553072715)
              ·
                refine ⟨25793227179314562829609073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17195484786209708553072715 25793227179314562829609073)
                ·
                  refine ⟨19344920384485922122206805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25793227179314562829609073 19344920384485922122206805)
                  ·
                    refine ⟨226698285755694399869611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19344920384485922122206805 226698285755694399869611)
                    ·
                      rfl

theorem cell23_1324480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_1324480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324480 prefixEnd_1324480 := by exact prefixLift 1324480
  have htrace : WordTrace (prefixWord ++ tailWord_1324480) baseStart_1324480 baseEnd_1324480 := by
    simpa [prefixWord, tailWord_1324480, baseEnd_1324480] using wordTrace_append hprefix tailTrace_1324480
  have hstable : (prefixWord ++ tailWord_1324480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324480).length < 2 ^ (prefixWord ++ tailWord_1324480).sum := by decide
  have hdescent : baseEnd_1324480 < baseStart_1324480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324482 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1324482 : Nat := 118140960795 + 1324482 * 2 ^ 59
def prefixEnd_1324482 : Nat := 4983230072969 + 3 ^ 40 * 1324482 * 2
def baseEnd_1324482 : Nat := 680095884228392191783825

theorem tailTrace_1324482 : CollatzResearch.WordTrace tailWord_1324482 prefixEnd_1324482 680095884228392191783825 := by
  unfold tailWord_1324482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076956796908848090431925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32205218125090261574485133 12076956796908848090431925)
  ·
    refine ⟨1132214699710204508477993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12076956796908848090431925 1132214699710204508477993)
    ·
      refine ⟨849161024782653381358495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1132214699710204508477993 849161024782653381358495)
      ·
        refine ⟨1273741537173980072037743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849161024782653381358495 1273741537173980072037743)
        ·
          refine ⟨1910612305760970108056615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273741537173980072037743 1910612305760970108056615)
          ·
            refine ⟨2865918458641455162084923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910612305760970108056615 2865918458641455162084923)
            ·
              refine ⟨4298877687962182743127385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865918458641455162084923 4298877687962182743127385)
              ·
                refine ⟨3224158265971637057345539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4298877687962182743127385 3224158265971637057345539)
                ·
                  refine ⟨4836237398957455586018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224158265971637057345539 4836237398957455586018309)
                  ·
                    refine ⟨906794512304522922378433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836237398957455586018309 906794512304522922378433)
                    ·
                      refine ⟨680095884228392191783825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906794512304522922378433 680095884228392191783825)
                      ·
                        rfl

theorem cell23_1324482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1324482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324482 prefixEnd_1324482 := by exact prefixLift 1324482
  have htrace : WordTrace (prefixWord ++ tailWord_1324482) baseStart_1324482 baseEnd_1324482 := by
    simpa [prefixWord, tailWord_1324482, baseEnd_1324482] using wordTrace_append hprefix tailTrace_1324482
  have hstable : (prefixWord ++ tailWord_1324482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324482).length < 2 ^ (prefixWord ++ tailWord_1324482).sum := by decide
  have hdescent : baseEnd_1324482 < baseStart_1324482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324484 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1324484 : Nat := 118140960795 + 1324484 * 2 ^ 59
def prefixEnd_1324484 : Nat := 4983230072969 + 3 ^ 40 * 1324484 * 2
def baseEnd_1324484 : Nat := 226698970396567061319605

theorem tailTrace_1324484 : CollatzResearch.WordTrace tailWord_1324484 prefixEnd_1324484 226698970396567061319605 := by
  unfold tailWord_1324484
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153950066814073351650253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32205266755752097802200337 24153950066814073351650253)
  ·
    refine ⟨9057731275055277506868845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24153950066814073351650253 9057731275055277506868845)
    ·
      refine ⟨3396649228145729065075817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9057731275055277506868845 3396649228145729065075817)
      ·
        refine ⟨2547486921109296798806863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3396649228145729065075817 2547486921109296798806863)
        ·
          refine ⟨3821230381663945198210295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547486921109296798806863 3821230381663945198210295)
          ·
            refine ⟨5731845572495917797315443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821230381663945198210295 5731845572495917797315443)
            ·
              refine ⟨8597768358743876695973165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731845572495917797315443 8597768358743876695973165)
              ·
                refine ⟨3224163134528953760989937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8597768358743876695973165 3224163134528953760989937)
                ·
                  refine ⟨2418122350896715320742453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3224163134528953760989937 2418122350896715320742453)
                  ·
                    refine ⟨226698970396567061319605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2418122350896715320742453 226698970396567061319605)
                    ·
                      rfl

theorem cell23_1324484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1324484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324484 prefixEnd_1324484 := by exact prefixLift 1324484
  have htrace : WordTrace (prefixWord ++ tailWord_1324484) baseStart_1324484 baseEnd_1324484 := by
    simpa [prefixWord, tailWord_1324484, baseEnd_1324484] using wordTrace_append hprefix tailTrace_1324484
  have hstable : (prefixWord ++ tailWord_1324484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324484).length < 2 ^ (prefixWord ++ tailWord_1324484).sum := by decide
  have hdescent : baseEnd_1324484 < baseStart_1324484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324527 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 6]
def baseStart_1324527 : Nat := 118140960795 + 1324527 * 2 ^ 59
def prefixEnd_1324527 : Nat := 4983230072969 + 3 ^ 40 * 1324527 * 2
def baseEnd_1324527 : Nat := 75568776761982723969013

theorem tailTrace_1324527 : CollatzResearch.WordTrace tailWord_1324527 prefixEnd_1324527 75568776761982723969013 := by
  unfold tailWord_1324527
  simp only [CollatzResearch.WordTrace]
  refine ⟨48309468472472365047115835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32206312314981576698077223 48309468472472365047115835)
  ·
    refine ⟨72464202708708547570673753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48309468472472365047115835 72464202708708547570673753)
    ·
      refine ⟨54348152031531410678005315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72464202708708547570673753 54348152031531410678005315)
      ·
        refine ⟨81522228047297116017007973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54348152031531410678005315 81522228047297116017007973)
        ·
          refine ⟨15285417758868209253188995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81522228047297116017007973 15285417758868209253188995)
          ·
            refine ⟨22928126638302313879783493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15285417758868209253188995 22928126638302313879783493)
            ·
              refine ⟨4299023744681683852459405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22928126638302313879783493 4299023744681683852459405)
              ·
                refine ⟨1612133904255631444672277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4299023744681683852459405 1612133904255631444672277)
                ·
                  refine ⟨75568776761982723969013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1612133904255631444672277 75568776761982723969013)
                  ·
                    rfl

theorem cell23_1324527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 6].length) (baseStart_1324527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324527 prefixEnd_1324527 := by exact prefixLift 1324527
  have htrace : WordTrace (prefixWord ++ tailWord_1324527) baseStart_1324527 baseEnd_1324527 := by
    simpa [prefixWord, tailWord_1324527, baseEnd_1324527] using wordTrace_append hprefix tailTrace_1324527
  have hstable : (prefixWord ++ tailWord_1324527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324527).length < 2 ^ (prefixWord ++ tailWord_1324527).sum := by decide
  have hdescent : baseEnd_1324527 < baseStart_1324527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324541 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_1324541 : Nat := 118140960795 + 1324541 * 2 ^ 59
def prefixEnd_1324541 : Nat := 4983230072969 + 3 ^ 40 * 1324541 * 2
def baseEnd_1324541 : Nat := 680126179587007460946053

theorem tailTrace_1324541 : CollatzResearch.WordTrace tailWord_1324541 prefixEnd_1324541 680126179587007460946053 := by
  unfold tailWord_1324541
  simp only [CollatzResearch.WordTrace]
  refine ⟨48309979094421645438125477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32206652729614430292083651 48309979094421645438125477)
  ·
    refine ⟨9058121080204058519648527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48309979094421645438125477 9058121080204058519648527)
    ·
      refine ⟨13587181620306087779472791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9058121080204058519648527 13587181620306087779472791)
      ·
        refine ⟨20380772430459131669209187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13587181620306087779472791 20380772430459131669209187)
        ·
          refine ⟨30571158645688697503813781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20380772430459131669209187 30571158645688697503813781)
          ·
            refine ⟨1433023061516657695491271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30571158645688697503813781 1433023061516657695491271)
            ·
              refine ⟨2149534592274986543236907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433023061516657695491271 2149534592274986543236907)
              ·
                refine ⟨3224301888412479814855361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149534592274986543236907 3224301888412479814855361)
                ·
                  refine ⟨2418226416309359861141521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3224301888412479814855361 2418226416309359861141521)
                  ·
                    refine ⟨1813669812232019895856141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418226416309359861141521 1813669812232019895856141)
                    ·
                      refine ⟨680126179587007460946053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1813669812232019895856141 680126179587007460946053)
                      ·
                        rfl

theorem cell23_1324541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_1324541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324541 prefixEnd_1324541 := by exact prefixLift 1324541
  have htrace : WordTrace (prefixWord ++ tailWord_1324541) baseStart_1324541 baseEnd_1324541 := by
    simpa [prefixWord, tailWord_1324541, baseEnd_1324541] using wordTrace_append hprefix tailTrace_1324541
  have hstable : (prefixWord ++ tailWord_1324541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324541).length < 2 ^ (prefixWord ++ tailWord_1324541).sum := by decide
  have hdescent : baseEnd_1324541 < baseStart_1324541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324594 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_1324594 : Nat := 118140960795 + 1324594 * 2 ^ 59
def prefixEnd_1324594 : Nat := 4983230072969 + 3 ^ 40 * 1324594 * 2
def baseEnd_1324594 : Nat := 680153394061695753583309

theorem tailTrace_1324594 : CollatzResearch.WordTrace tailWord_1324594 prefixEnd_1324594 680153394061695753583309 := by
  unfold tailWord_1324594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12077978040807408872451209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32207941442153090326536557 12077978040807408872451209)
  ·
    refine ⟨9058483530605556654338407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12077978040807408872451209 9058483530605556654338407)
    ·
      refine ⟨13587725295908334981507611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9058483530605556654338407 13587725295908334981507611)
      ·
        refine ⟨20381587943862502472261417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13587725295908334981507611 20381587943862502472261417)
        ·
          refine ⟨15286190957896876854196063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20381587943862502472261417 15286190957896876854196063)
          ·
            refine ⟨22929286436845315281294095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15286190957896876854196063 22929286436845315281294095)
            ·
              refine ⟨34393929655267972921941143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22929286436845315281294095 34393929655267972921941143)
              ·
                refine ⟨51590894482901959382911715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34393929655267972921941143 51590894482901959382911715)
                ·
                  refine ⟨77386341724352939074367573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51590894482901959382911715 77386341724352939074367573)
                  ·
                    refine ⟨906871192082261004777745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77386341724352939074367573 906871192082261004777745)
                    ·
                      refine ⟨680153394061695753583309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 906871192082261004777745 680153394061695753583309)
                      ·
                        rfl

theorem cell23_1324594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_1324594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324594 prefixEnd_1324594 := by exact prefixLift 1324594
  have htrace : WordTrace (prefixWord ++ tailWord_1324594) baseStart_1324594 baseEnd_1324594 := by
    simpa [prefixWord, tailWord_1324594, baseEnd_1324594] using wordTrace_append hprefix tailTrace_1324594
  have hstable : (prefixWord ++ tailWord_1324594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324594).length < 2 ^ (prefixWord ++ tailWord_1324594).sum := by decide
  have hdescent : baseEnd_1324594 < baseStart_1324594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
