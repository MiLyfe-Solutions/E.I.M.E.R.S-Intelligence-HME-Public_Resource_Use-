import V185TrunkScan22Chunk373

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3334106 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_3334106 : Nat := 118140960795 + 3334106 * 2 ^ 59
def prefixEnd_3334106 : Nat := 4983230072969 + 3 ^ 40 * 3334106 * 2
def baseEnd_3334106 : Nat := 380444206897652784142607

theorem tailTrace_3334106 : CollatzResearch.WordTrace tailWord_3334106 prefixEnd_3334106 380444206897652784142607 := by
  unfold tailWord_3334106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30401209014777714204017543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81069890706073904544046781 30401209014777714204017543)
  ·
    refine ⟨45601813522166571306026315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30401209014777714204017543 45601813522166571306026315)
    ·
      refine ⟨68402720283249856959039473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45601813522166571306026315 68402720283249856959039473)
      ·
        refine ⟨51302040212437392719279605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68402720283249856959039473 51302040212437392719279605)
        ·
          refine ⟨4809566269916005567432463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51302040212437392719279605 4809566269916005567432463)
          ·
            refine ⟨7214349404874008351148695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809566269916005567432463 7214349404874008351148695)
            ·
              refine ⟨10821524107311012526723043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214349404874008351148695 10821524107311012526723043)
              ·
                refine ⟨16232286160966518790084565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10821524107311012526723043 16232286160966518790084565)
                ·
                  refine ⟨380444206897652784142607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16232286160966518790084565 380444206897652784142607)
                  ·
                    rfl

theorem cell22_3334106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_3334106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334106 prefixEnd_3334106 := by exact prefixLift 3334106
  have htrace : WordTrace (prefixWord ++ tailWord_3334106) baseStart_3334106 baseEnd_3334106 := by
    simpa [prefixWord, tailWord_3334106, baseEnd_3334106] using wordTrace_append hprefix tailTrace_3334106
  have hstable : (prefixWord ++ tailWord_3334106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334106).length < 2 ^ (prefixWord ++ tailWord_3334106).sum := by decide
  have hdescent : baseEnd_3334106 < baseStart_3334106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334136 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_3334136 : Nat := 118140960795 + 3334136 * 2 ^ 59
def prefixEnd_3334136 : Nat := 4983230072969 + 3 ^ 40 * 3334136 * 2
def baseEnd_3334136 : Nat := 1141342890306048274177729

theorem tailTrace_3334136 : CollatzResearch.WordTrace tailWord_3334136 prefixEnd_3334136 1141342890306048274177729 := by
  unfold tailWord_3334136
  simp only [CollatzResearch.WordTrace]
  refine ⟨60802965124501085969831131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81070620166001447959774841 60802965124501085969831131)
  ·
    refine ⟨91204447686751628954746697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60802965124501085969831131 91204447686751628954746697)
    ·
      refine ⟨68403335765063721716060023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91204447686751628954746697 68403335765063721716060023)
      ·
        refine ⟨102605003647595582574090035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68403335765063721716060023 102605003647595582574090035)
        ·
          refine ⟨153907505471393373861135053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102605003647595582574090035 153907505471393373861135053)
          ·
            refine ⟨57715314551772515197925645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153907505471393373861135053 57715314551772515197925645)
            ·
              refine ⟨21643242956914693199222117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57715314551772515197925645 21643242956914693199222117)
              ·
                refine ⟨4058108054421504974854147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21643242956914693199222117 4058108054421504974854147)
                ·
                  refine ⟨6087162081632257462281221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058108054421504974854147 6087162081632257462281221)
                  ·
                    refine ⟨1141342890306048274177729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6087162081632257462281221 1141342890306048274177729)
                    ·
                      rfl

theorem cell22_3334136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_3334136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334136 prefixEnd_3334136 := by exact prefixLift 3334136
  have htrace : WordTrace (prefixWord ++ tailWord_3334136) baseStart_3334136 baseEnd_3334136 := by
    simpa [prefixWord, tailWord_3334136, baseEnd_3334136] using wordTrace_append hprefix tailTrace_3334136
  have hstable : (prefixWord ++ tailWord_3334136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334136).length < 2 ^ (prefixWord ++ tailWord_3334136).sum := by decide
  have hdescent : baseEnd_3334136 < baseStart_3334136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334211 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 7, 3]
def baseStart_3334211 : Nat := 118140960795 + 3334211 * 2 ^ 59
def prefixEnd_3334211 : Nat := 4983230072969 + 3 ^ 40 * 3334211 * 2
def baseEnd_3334211 : Nat := 1141368564338773078552499

theorem tailTrace_3334211 : CollatzResearch.WordTrace tailWord_3334211 prefixEnd_3334211 1141368564338773078552499 := by
  unfold tailWord_3334211
  simp only [CollatzResearch.WordTrace]
  refine ⟨121608665723730459748642487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81072443815820306499094991 121608665723730459748642487)
  ·
    refine ⟨182412998585595689622963731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121608665723730459748642487 182412998585595689622963731)
    ·
      refine ⟨273619497878393534434445597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182412998585595689622963731 273619497878393534434445597)
      ·
        refine ⟨102607311704397575412917099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273619497878393534434445597 102607311704397575412917099)
        ·
          refine ⟨153910967556596363119375649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102607311704397575412917099 153910967556596363119375649)
          ·
            refine ⟨115433225667447272339531737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153910967556596363119375649 115433225667447272339531737)
            ·
              refine ⟨86574919250585454254648803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115433225667447272339531737 86574919250585454254648803)
              ·
                refine ⟨129862378875878181381973205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86574919250585454254648803 129862378875878181381973205)
                ·
                  refine ⟨3043649504903394876139997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129862378875878181381973205 3043649504903394876139997)
                  ·
                    refine ⟨1141368564338773078552499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043649504903394876139997 1141368564338773078552499)
                    ·
                      rfl

theorem cell22_3334211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 3].length) (baseStart_3334211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334211 prefixEnd_3334211 := by exact prefixLift 3334211
  have htrace : WordTrace (prefixWord ++ tailWord_3334211) baseStart_3334211 baseEnd_3334211 := by
    simpa [prefixWord, tailWord_3334211, baseEnd_3334211] using wordTrace_append hprefix tailTrace_3334211
  have hstable : (prefixWord ++ tailWord_3334211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334211).length < 2 ^ (prefixWord ++ tailWord_3334211).sum := by decide
  have hdescent : baseEnd_3334211 < baseStart_3334211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334228 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3334228 : Nat := 118140960795 + 3334228 * 2 ^ 59
def prefixEnd_3334228 : Nat := 4983230072969 + 3 ^ 40 * 3334228 * 2
def baseEnd_3334228 : Nat := 1141374383786190700877447

theorem tailTrace_3334228 : CollatzResearch.WordTrace tailWord_3334228 prefixEnd_3334228 1141374383786190700877447 := by
  unfold tailWord_3334228
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804642882334435826005669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81072857176445914434674225 60804642882334435826005669)
  ·
    refine ⟨11400870540437706717376063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60804642882334435826005669 11400870540437706717376063)
    ·
      refine ⟨17101305810656560076064095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11400870540437706717376063 17101305810656560076064095)
      ·
        refine ⟨25651958715984840114096143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17101305810656560076064095 25651958715984840114096143)
        ·
          refine ⟨38477938073977260171144215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25651958715984840114096143 38477938073977260171144215)
          ·
            refine ⟨57716907110965890256716323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38477938073977260171144215 57716907110965890256716323)
            ·
              refine ⟨86575360666448835385074485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57716907110965890256716323 86575360666448835385074485)
              ·
                refine ⟨8116440062479578317350733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86575360666448835385074485 8116440062479578317350733)
                ·
                  refine ⟨3043665023429841869006525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8116440062479578317350733 3043665023429841869006525)
                  ·
                    refine ⟨1141374383786190700877447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043665023429841869006525 1141374383786190700877447)
                    ·
                      rfl

theorem cell22_3334228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3334228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334228 prefixEnd_3334228 := by exact prefixLift 3334228
  have htrace : WordTrace (prefixWord ++ tailWord_3334228) baseStart_3334228 baseEnd_3334228 := by
    simpa [prefixWord, tailWord_3334228, baseEnd_3334228] using wordTrace_append hprefix tailTrace_3334228
  have hstable : (prefixWord ++ tailWord_3334228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334228).length < 2 ^ (prefixWord ++ tailWord_3334228).sum := by decide
  have hdescent : baseEnd_3334228 < baseStart_3334228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334230 : List Nat := [5, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3334230 : Nat := 118140960795 + 3334230 * 2 ^ 59
def prefixEnd_3334230 : Nat := 4983230072969 + 3 ^ 40 * 3334230 * 2
def baseEnd_3334230 : Nat := 126819452047451484703049

theorem tailTrace_3334230 : CollatzResearch.WordTrace tailWord_3334230 prefixEnd_3334230 126819452047451484703049 := by
  unfold tailWord_3334230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600584919416351624599009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81072905807107750662389429 7600584919416351624599009)
  ·
    refine ⟨5700438689562263718449257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7600584919416351624599009 5700438689562263718449257)
    ·
      refine ⟨4275329017171697788836943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700438689562263718449257 4275329017171697788836943)
      ·
        refine ⟨6412993525757546683255415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275329017171697788836943 6412993525757546683255415)
        ·
          refine ⟨9619490288636320024883123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6412993525757546683255415 9619490288636320024883123)
          ·
            refine ⟨14429235432954480037324685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9619490288636320024883123 14429235432954480037324685)
            ·
              refine ⟨5410963287357930013996757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14429235432954480037324685 5410963287357930013996757)
              ·
                refine ⟨126819452047451484703049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5410963287357930013996757 126819452047451484703049)
                ·
                  rfl

theorem cell22_3334230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3334230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334230 prefixEnd_3334230 := by exact prefixLift 3334230
  have htrace : WordTrace (prefixWord ++ tailWord_3334230) baseStart_3334230 baseEnd_3334230 := by
    simpa [prefixWord, tailWord_3334230, baseEnd_3334230] using wordTrace_append hprefix tailTrace_3334230
  have hstable : (prefixWord ++ tailWord_3334230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334230).length < 2 ^ (prefixWord ++ tailWord_3334230).sum := by decide
  have hdescent : baseEnd_3334230 < baseStart_3334230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334262 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_3334262 : Nat := 118140960795 + 3334262 * 2 ^ 59
def prefixEnd_3334262 : Nat := 4983230072969 + 3 ^ 40 * 3334262 * 2
def baseEnd_3334262 : Nat := 1141386022681025945527343

theorem tailTrace_3334262 : CollatzResearch.WordTrace tailWord_3334262 prefixEnd_3334262 1141386022681025945527343 := by
  unfold tailWord_3334262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600657865409105966171815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81073683897697130305832693 7600657865409105966171815)
  ·
    refine ⟨11400986798113658949257723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7600657865409105966171815 11400986798113658949257723)
    ·
      refine ⟨17101480197170488423886585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11400986798113658949257723 17101480197170488423886585)
      ·
        refine ⟨12826110147877866317914939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17101480197170488423886585 12826110147877866317914939)
        ·
          refine ⟨19239165221816799476872409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12826110147877866317914939 19239165221816799476872409)
          ·
            refine ⟨14429373916362599607654307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19239165221816799476872409 14429373916362599607654307)
            ·
              refine ⟨21644060874543899411481461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14429373916362599607654307 21644060874543899411481461)
              ·
                refine ⟨2029130706988490569826387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21644060874543899411481461 2029130706988490569826387)
                ·
                  refine ⟨3043696060482735854739581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029130706988490569826387 3043696060482735854739581)
                  ·
                    refine ⟨1141386022681025945527343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043696060482735854739581 1141386022681025945527343)
                    ·
                      rfl

theorem cell22_3334262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_3334262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334262 prefixEnd_3334262 := by exact prefixLift 3334262
  have htrace : WordTrace (prefixWord ++ tailWord_3334262) baseStart_3334262 baseEnd_3334262 := by
    simpa [prefixWord, tailWord_3334262, baseEnd_3334262] using wordTrace_append hprefix tailTrace_3334262
  have hstable : (prefixWord ++ tailWord_3334262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334262).length < 2 ^ (prefixWord ++ tailWord_3334262).sum := by decide
  have hdescent : baseEnd_3334262 < baseStart_3334262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334303 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 6]
def baseStart_3334303 : Nat := 118140960795 + 3334303 * 2 ^ 59
def prefixEnd_3334303 : Nat := 4983230072969 + 3 ^ 40 * 3334303 * 2
def baseEnd_3334303 : Nat := 380466685939638501750739

theorem tailTrace_3334303 : CollatzResearch.WordTrace tailWord_3334303 prefixEnd_3334303 380466685939638501750739 := by
  unfold tailWord_3334303
  simp only [CollatzResearch.WordTrace]
  refine ⟨121612021239397159460991563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81074680826264772973994375 121612021239397159460991563)
  ·
    refine ⟨182418031859095739191487345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121612021239397159460991563 182418031859095739191487345)
    ·
      refine ⟨136813523894321804393615509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182418031859095739191487345 136813523894321804393615509)
      ·
        refine ⟨6413133932546334580950727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136813523894321804393615509 6413133932546334580950727)
        ·
          refine ⟨9619700898819501871426091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413133932546334580950727 9619700898819501871426091)
          ·
            refine ⟨14429551348229252807139137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9619700898819501871426091 14429551348229252807139137)
            ·
              refine ⟨10822163511171939605354353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14429551348229252807139137 10822163511171939605354353)
              ·
                refine ⟨8116622633378954704015765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10822163511171939605354353 8116622633378954704015765)
                ·
                  refine ⟨380466685939638501750739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8116622633378954704015765 380466685939638501750739)
                  ·
                    rfl

theorem cell22_3334303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 6].length) (baseStart_3334303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334303 prefixEnd_3334303 := by exact prefixLift 3334303
  have htrace : WordTrace (prefixWord ++ tailWord_3334303) baseStart_3334303 baseEnd_3334303 := by
    simpa [prefixWord, tailWord_3334303, baseEnd_3334303] using wordTrace_append hprefix tailTrace_3334303
  have hstable : (prefixWord ++ tailWord_3334303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334303).length < 2 ^ (prefixWord ++ tailWord_3334303).sum := by decide
  have hdescent : baseEnd_3334303 < baseStart_3334303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334305 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3334305 : Nat := 118140960795 + 3334305 * 2 ^ 59
def prefixEnd_3334305 : Nat := 4983230072969 + 3 ^ 40 * 3334305 * 2
def baseEnd_3334305 : Nat := 1141400742459788166702211

theorem tailTrace_3334305 : CollatzResearch.WordTrace tailWord_3334305 prefixEnd_3334305 1141400742459788166702211 := by
  unfold tailWord_3334305
  simp only [CollatzResearch.WordTrace]
  refine ⟨121612094185389913802564369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81074729456926609201709579 121612094185389913802564369)
  ·
    refine ⟨91209070639042435351923277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121612094185389913802564369 91209070639042435351923277)
    ·
      refine ⟨34203401489640913256971229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91209070639042435351923277 34203401489640913256971229)
      ·
        refine ⟨12826275558615342471364211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34203401489640913256971229 12826275558615342471364211)
        ·
          refine ⟨19239413337923013707046317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12826275558615342471364211 19239413337923013707046317)
          ·
            refine ⟨7214780001721130140142369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19239413337923013707046317 7214780001721130140142369)
            ·
              refine ⟨5411085001290847605106777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7214780001721130140142369 5411085001290847605106777)
              ·
                refine ⟨4058313750968135703830083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5411085001290847605106777 4058313750968135703830083)
                ·
                  refine ⟨6087470626452203555745125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058313750968135703830083 6087470626452203555745125)
                  ·
                    refine ⟨1141400742459788166702211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6087470626452203555745125 1141400742459788166702211)
                    ·
                      rfl

theorem cell22_3334305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3334305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334305 prefixEnd_3334305 := by exact prefixLift 3334305
  have htrace : WordTrace (prefixWord ++ tailWord_3334305) baseStart_3334305 baseEnd_3334305 := by
    simpa [prefixWord, tailWord_3334305, baseEnd_3334305] using wordTrace_append hprefix tailTrace_3334305
  have hstable : (prefixWord ++ tailWord_3334305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334305).length < 2 ^ (prefixWord ++ tailWord_3334305).sum := by decide
  have hdescent : baseEnd_3334305 < baseStart_3334305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334337 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 6]
def baseStart_3334337 : Nat := 118140960795 + 3334337 * 2 ^ 59
def prefixEnd_3334337 : Nat := 4983230072969 + 3 ^ 40 * 3334337 * 2
def baseEnd_3334337 : Nat := 380470565571250249967371

theorem tailTrace_3334337 : CollatzResearch.WordTrace tailWord_3334337 prefixEnd_3334337 380470565571250249967371 := by
  unfold tailWord_3334337
  simp only [CollatzResearch.WordTrace]
  refine ⟨121613261321273983267729265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81075507547515988845152843 121613261321273983267729265)
  ·
    refine ⟨91209945990955487450796949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121613261321273983267729265 91209945990955487450796949)
    ·
      refine ⟨4275466218326038474256107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91209945990955487450796949 4275466218326038474256107)
      ·
        refine ⟨6413199327489057711384161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275466218326038474256107 6413199327489057711384161)
        ·
          refine ⟨4809899495616793283538121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413199327489057711384161 4809899495616793283538121)
          ·
            refine ⟨3607424621712594962653591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809899495616793283538121 3607424621712594962653591)
            ·
              refine ⟨5411136932568892443980387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607424621712594962653591 5411136932568892443980387)
              ·
                refine ⟨8116705398853338665970581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411136932568892443980387 8116705398853338665970581)
                ·
                  refine ⟨380470565571250249967371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8116705398853338665970581 380470565571250249967371)
                  ·
                    rfl

theorem cell22_3334337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_3334337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334337 prefixEnd_3334337 := by exact prefixLift 3334337
  have htrace : WordTrace (prefixWord ++ tailWord_3334337) baseStart_3334337 baseEnd_3334337 := by
    simpa [prefixWord, tailWord_3334337, baseEnd_3334337] using wordTrace_append hprefix tailTrace_3334337
  have hstable : (prefixWord ++ tailWord_3334337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334337).length < 2 ^ (prefixWord ++ tailWord_3334337).sum := by decide
  have hdescent : baseEnd_3334337 < baseStart_3334337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334408 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3334408 : Nat := 118140960795 + 3334408 * 2 ^ 59
def prefixEnd_3334408 : Nat := 4983230072969 + 3 ^ 40 * 3334408 * 2
def baseEnd_3334408 : Nat := 1141436001464730231376895

theorem tailTrace_3334408 : CollatzResearch.WordTrace tailWord_3334408 prefixEnd_3334408 1141436001464730231376895 := by
  unfold tailWord_3334408
  simp only [CollatzResearch.WordTrace]
  refine ⟨60807925452008381196781939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81077233936011174929042585 60807925452008381196781939)
  ·
    refine ⟨91211888178012571795172909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60807925452008381196781939 91211888178012571795172909)
    ·
      refine ⟨34204458066754714423189841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91211888178012571795172909 34204458066754714423189841)
      ·
        refine ⟨25653343550066035817392381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34204458066754714423189841 25653343550066035817392381)
        ·
          refine ⟨9620003831274763431522143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25653343550066035817392381 9620003831274763431522143)
          ·
            refine ⟨14430005746912145147283215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620003831274763431522143 14430005746912145147283215)
            ·
              refine ⟨21645008620368217720924823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14430005746912145147283215 21645008620368217720924823)
              ·
                refine ⟨32467512930552326581387235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21645008620368217720924823 32467512930552326581387235)
                ·
                  refine ⟨48701269395828489872080853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32467512930552326581387235 48701269395828489872080853)
                  ·
                    refine ⟨1141436001464730231376895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48701269395828489872080853 1141436001464730231376895)
                    ·
                      rfl

theorem cell22_3334408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3334408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334408 prefixEnd_3334408 := by exact prefixLift 3334408
  have htrace : WordTrace (prefixWord ++ tailWord_3334408) baseStart_3334408 baseEnd_3334408 := by
    simpa [prefixWord, tailWord_3334408, baseEnd_3334408] using wordTrace_append hprefix tailTrace_3334408
  have hstable : (prefixWord ++ tailWord_3334408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334408).length < 2 ^ (prefixWord ++ tailWord_3334408).sum := by decide
  have hdescent : baseEnd_3334408 < baseStart_3334408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334513 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_3334513 : Nat := 118140960795 + 3334513 * 2 ^ 59
def prefixEnd_3334513 : Nat := 4983230072969 + 3 ^ 40 * 3334513 * 2
def baseEnd_3334513 : Nat := 1141471945110544957501573

theorem tailTrace_3334513 : CollatzResearch.WordTrace tailWord_3334513 prefixEnd_3334513 1141471945110544957501573 := by
  unfold tailWord_3334513
  simp only [CollatzResearch.WordTrace]
  refine ⟨121619680568636365326136193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81079787045757576884090795 121619680568636365326136193)
  ·
    refine ⟨91214760426477273994602145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121619680568636365326136193 91214760426477273994602145)
    ·
      refine ⟨68411070319857955495951609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91214760426477273994602145 68411070319857955495951609)
      ·
        refine ⟨51308302739893466621963707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68411070319857955495951609 51308302739893466621963707)
        ·
          refine ⟨76962454109840199932945561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51308302739893466621963707 76962454109840199932945561)
          ·
            refine ⟨57721840582380149949709171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76962454109840199932945561 57721840582380149949709171)
            ·
              refine ⟨86582760873570224924563757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57721840582380149949709171 86582760873570224924563757)
              ·
                refine ⟨32468535327588834346711409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86582760873570224924563757 32468535327588834346711409)
                ·
                  refine ⟨24351401495691625760033557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32468535327588834346711409 24351401495691625760033557)
                  ·
                    refine ⟨1141471945110544957501573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24351401495691625760033557 1141471945110544957501573)
                    ·
                      rfl

theorem cell22_3334513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_3334513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334513 prefixEnd_3334513 := by exact prefixLift 3334513
  have htrace : WordTrace (prefixWord ++ tailWord_3334513) baseStart_3334513 baseEnd_3334513 := by
    simpa [prefixWord, tailWord_3334513, baseEnd_3334513] using wordTrace_append hprefix tailTrace_3334513
  have hstable : (prefixWord ++ tailWord_3334513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334513).length < 2 ^ (prefixWord ++ tailWord_3334513).sum := by decide
  have hdescent : baseEnd_3334513 < baseStart_3334513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334562 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3334562 : Nat := 118140960795 + 3334562 * 2 ^ 59
def prefixEnd_3334562 : Nat := 4983230072969 + 3 ^ 40 * 3334562 * 2
def baseEnd_3334562 : Nat := 380496239603975054342141

theorem tailTrace_3334562 : CollatzResearch.WordTrace tailWord_3334562 prefixEnd_3334562 380496239603975054342141 := by
  unfold tailWord_3334562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30405366936364711673667485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81080978496972564463113293 30405366936364711673667485)
  ·
    refine ⟨11402012601136766877625307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30405366936364711673667485 11402012601136766877625307)
    ·
      refine ⟨17103018901705150316437961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11402012601136766877625307 17103018901705150316437961)
      ·
        refine ⟨12827264176278862737328471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17103018901705150316437961 12827264176278862737328471)
        ·
          refine ⟨19240896264418294105992707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827264176278862737328471 19240896264418294105992707)
          ·
            refine ⟨28861344396627441158989061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19240896264418294105992707 28861344396627441158989061)
            ·
              refine ⟨5411502074367645217310449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28861344396627441158989061 5411502074367645217310449)
              ·
                refine ⟨4058626555775733912982837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5411502074367645217310449 4058626555775733912982837)
                ·
                  refine ⟨380496239603975054342141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4058626555775733912982837 380496239603975054342141)
                  ·
                    rfl

theorem cell22_3334562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3334562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334562 prefixEnd_3334562 := by exact prefixLift 3334562
  have htrace : WordTrace (prefixWord ++ tailWord_3334562) baseStart_3334562 baseEnd_3334562 := by
    simpa [prefixWord, tailWord_3334562, baseEnd_3334562] using wordTrace_append hprefix tailTrace_3334562
  have hstable : (prefixWord ++ tailWord_3334562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334562).length < 2 ^ (prefixWord ++ tailWord_3334562).sum := by decide
  have hdescent : baseEnd_3334562 < baseStart_3334562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334590 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_3334590 : Nat := 118140960795 + 3334590 * 2 ^ 59
def prefixEnd_3334590 : Nat := 4983230072969 + 3 ^ 40 * 3334590 * 2
def baseEnd_3334590 : Nat := 380499434594714141108779

theorem tailTrace_3334590 : CollatzResearch.WordTrace tailWord_3334590 prefixEnd_3334590 380499434594714141108779 := by
  unfold tailWord_3334590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202811123669675934586153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81081659326238271651126149 15202811123669675934586153)
  ·
    refine ⟨11402108342752256950939615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15202811123669675934586153 11402108342752256950939615)
    ·
      refine ⟨17103162514128385426409423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11402108342752256950939615 17103162514128385426409423)
      ·
        refine ⟨25654743771192578139614135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17103162514128385426409423 25654743771192578139614135)
        ·
          refine ⟨38482115656788867209421203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25654743771192578139614135 38482115656788867209421203)
          ·
            refine ⟨57723173485183300814131805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38482115656788867209421203 57723173485183300814131805)
            ·
              refine ⟨21646190056943737805299427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57723173485183300814131805 21646190056943737805299427)
              ·
                refine ⟨32469285085415606707949141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21646190056943737805299427 32469285085415606707949141)
                ·
                  refine ⟨380499434594714141108779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32469285085415606707949141 380499434594714141108779)
                  ·
                    rfl

theorem cell22_3334590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_3334590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334590 prefixEnd_3334590 := by exact prefixLift 3334590
  have htrace : WordTrace (prefixWord ++ tailWord_3334590) baseStart_3334590 baseEnd_3334590 := by
    simpa [prefixWord, tailWord_3334590, baseEnd_3334590] using wordTrace_append hprefix tailTrace_3334590
  have hstable : (prefixWord ++ tailWord_3334590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334590).length < 2 ^ (prefixWord ++ tailWord_3334590).sum := by decide
  have hdescent : baseEnd_3334590 < baseStart_3334590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334637 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3334637 : Nat := 118140960795 + 3334637 * 2 ^ 59
def prefixEnd_3334637 : Nat := 4983230072969 + 3 ^ 40 * 3334637 * 2
def baseEnd_3334637 : Nat := 1141514392844649967401193

theorem tailTrace_3334637 : CollatzResearch.WordTrace tailWord_3334637 prefixEnd_3334637 1141514392844649967401193 := by
  unfold tailWord_3334637
  simp only [CollatzResearch.WordTrace]
  refine ⟨121624203220187134503650165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81082802146791423002433443 121624203220187134503650165)
  ·
    refine ⟨11402269051892543859717203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121624203220187134503650165 11402269051892543859717203)
    ·
      refine ⟨17103403577838815789575805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11402269051892543859717203 17103403577838815789575805)
      ·
        refine ⟨6413776341689555921090927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17103403577838815789575805 6413776341689555921090927)
        ·
          refine ⟨9620664512534333881636391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413776341689555921090927 9620664512534333881636391)
          ·
            refine ⟨14430996768801500822454587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620664512534333881636391 14430996768801500822454587)
            ·
              refine ⟨21646495153202251233681881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14430996768801500822454587 21646495153202251233681881)
              ·
                refine ⟨16234871364901688425261411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21646495153202251233681881 16234871364901688425261411)
                ·
                  refine ⟨24352307047352532637892117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16234871364901688425261411 24352307047352532637892117)
                  ·
                    refine ⟨1141514392844649967401193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24352307047352532637892117 1141514392844649967401193)
                    ·
                      rfl

theorem cell22_3334637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3334637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334637 prefixEnd_3334637 := by exact prefixLift 3334637
  have htrace : WordTrace (prefixWord ++ tailWord_3334637) baseStart_3334637 baseEnd_3334637 := by
    simpa [prefixWord, tailWord_3334637, baseEnd_3334637] using wordTrace_append hprefix tailTrace_3334637
  have hstable : (prefixWord ++ tailWord_3334637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334637).length < 2 ^ (prefixWord ++ tailWord_3334637).sum := by decide
  have hdescent : baseEnd_3334637 < baseStart_3334637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334658 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3334658 : Nat := 118140960795 + 3334658 * 2 ^ 59
def prefixEnd_3334658 : Nat := 4983230072969 + 3 ^ 40 * 3334658 * 2
def baseEnd_3334658 : Nat := 380507193857937637542043

theorem tailTrace_3334658 : CollatzResearch.WordTrace tailWord_3334658 prefixEnd_3334658 380507193857937637542043 := by
  unfold tailWord_3334658
  simp only [CollatzResearch.WordTrace]
  refine ⟨30406242288277763772541157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81083312768740703393443085 30406242288277763772541157)
  ·
    refine ⟨5701170429052080707351467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30406242288277763772541157 5701170429052080707351467)
    ·
      refine ⟨8551755643578121061027201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5701170429052080707351467 8551755643578121061027201)
      ·
        refine ⟨6413816732683590795770401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8551755643578121061027201 6413816732683590795770401)
        ·
          refine ⟨4810362549512693096827801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413816732683590795770401 4810362549512693096827801)
          ·
            refine ⟨3607771912134519822620851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4810362549512693096827801 3607771912134519822620851)
            ·
              refine ⟨5411657868201779733931277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607771912134519822620851 5411657868201779733931277)
              ·
                refine ⟨2029371700575667400224229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5411657868201779733931277 2029371700575667400224229)
                ·
                  refine ⟨380507193857937637542043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2029371700575667400224229 380507193857937637542043)
                  ·
                    rfl

theorem cell22_3334658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3334658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334658 prefixEnd_3334658 := by exact prefixLift 3334658
  have htrace : WordTrace (prefixWord ++ tailWord_3334658) baseStart_3334658 baseEnd_3334658 := by
    simpa [prefixWord, tailWord_3334658, baseEnd_3334658] using wordTrace_append hprefix tailTrace_3334658
  have hstable : (prefixWord ++ tailWord_3334658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334658).length < 2 ^ (prefixWord ++ tailWord_3334658).sum := by decide
  have hdescent : baseEnd_3334658 < baseStart_3334658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334669 : List Nat := [1, 7, 1, 1, 1, 1, 10]
def baseStart_3334669 : Nat := 118140960795 + 3334669 * 2 ^ 59
def prefixEnd_3334669 : Nat := 4983230072969 + 3 ^ 40 * 3334669 * 2
def baseEnd_3334669 : Nat := 42278716559207872244485

theorem tailTrace_3334669 : CollatzResearch.WordTrace tailWord_3334669 prefixEnd_3334669 42278716559207872244485 := by
  unfold tailWord_3334669
  simp only [CollatzResearch.WordTrace]
  refine ⟨121625370356071203968815061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81083580237380802645876707 121625370356071203968815061)
  ·
    refine ⟨2850594617720418843019103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 121625370356071203968815061 2850594617720418843019103)
    ·
      refine ⟨4275891926580628264528655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850594617720418843019103 4275891926580628264528655)
      ·
        refine ⟨6413837889870942396792983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275891926580628264528655 6413837889870942396792983)
        ·
          refine ⟨9620756834806413595189475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413837889870942396792983 9620756834806413595189475)
          ·
            refine ⟨14431135252209620392784213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620756834806413595189475 14431135252209620392784213)
            ·
              refine ⟨42278716559207872244485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14431135252209620392784213 42278716559207872244485)
              ·
                rfl

theorem cell22_3334669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 10].length) (baseStart_3334669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334669 prefixEnd_3334669 := by exact prefixLift 3334669
  have htrace : WordTrace (prefixWord ++ tailWord_3334669) baseStart_3334669 baseEnd_3334669 := by
    simpa [prefixWord, tailWord_3334669, baseEnd_3334669] using wordTrace_append hprefix tailTrace_3334669
  have hstable : (prefixWord ++ tailWord_3334669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334669).length < 2 ^ (prefixWord ++ tailWord_3334669).sum := by decide
  have hdescent : baseEnd_3334669 < baseStart_3334669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334684 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_3334684 : Nat := 118140960795 + 3334684 * 2 ^ 59
def prefixEnd_3334684 : Nat := 4983230072969 + 3 ^ 40 * 3334684 * 2
def baseEnd_3334684 : Nat := 1141530481905157511476049

theorem tailTrace_3334684 : CollatzResearch.WordTrace tailWord_3334684 prefixEnd_3334684 1141530481905157511476049 := by
  unfold tailWord_3334684
  simp only [CollatzResearch.WordTrace]
  refine ⟨60812958725508430765305553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81083944967344574353740737 60812958725508430765305553)
  ·
    refine ⟨45609719044131323073979165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60812958725508430765305553 45609719044131323073979165)
    ·
      refine ⟨17103644641549246152742187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45609719044131323073979165 17103644641549246152742187)
      ·
        refine ⟨25655466962323869229113281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17103644641549246152742187 25655466962323869229113281)
        ·
          refine ⟨19241600221742901921834961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25655466962323869229113281 19241600221742901921834961)
          ·
            refine ⟨14431200166307176441376221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19241600221742901921834961 14431200166307176441376221)
            ·
              refine ⟨5411700062365191165516083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14431200166307176441376221 5411700062365191165516083)
              ·
                refine ⟨8117550093547786748274125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411700062365191165516083 8117550093547786748274125)
                ·
                  refine ⟨3044081285080420030602797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8117550093547786748274125 3044081285080420030602797)
                  ·
                    refine ⟨1141530481905157511476049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3044081285080420030602797 1141530481905157511476049)
                    ·
                      rfl

theorem cell22_3334684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_3334684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334684 prefixEnd_3334684 := by exact prefixLift 3334684
  have htrace : WordTrace (prefixWord ++ tailWord_3334684) baseStart_3334684 baseEnd_3334684 := by
    simpa [prefixWord, tailWord_3334684, baseEnd_3334684] using wordTrace_append hprefix tailTrace_3334684
  have hstable : (prefixWord ++ tailWord_3334684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334684).length < 2 ^ (prefixWord ++ tailWord_3334684).sum := by decide
  have hdescent : baseEnd_3334684 < baseStart_3334684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334838 : List Nat := [5, 1, 3, 1, 3, 1, 8]
def baseStart_3334838 : Nat := 118140960795 + 3334838 * 2 ^ 59
def prefixEnd_3334838 : Nat := 4983230072969 + 3 ^ 40 * 3334838 * 2
def baseEnd_3334838 : Nat := 42280859231568609004651

theorem tailTrace_3334838 : CollatzResearch.WordTrace tailWord_3334838 prefixEnd_3334838 42280859231568609004651 := by
  unfold tailWord_3334838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601970893278684114482323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81087689528305963887811445 7601970893278684114482323)
  ·
    refine ⟨11402956339918026171723485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7601970893278684114482323 11402956339918026171723485)
    ·
      refine ⟨4276108627469259814396307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11402956339918026171723485 4276108627469259814396307)
      ·
        refine ⟨6414162941203889721594461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276108627469259814396307 6414162941203889721594461)
        ·
          refine ⟨2405311102951458645597923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6414162941203889721594461 2405311102951458645597923)
          ·
            refine ⟨3607966654427187968396885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405311102951458645597923 3607966654427187968396885)
            ·
              refine ⟨42280859231568609004651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3607966654427187968396885 42280859231568609004651)
              ·
                rfl

theorem cell22_3334838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 8].length) (baseStart_3334838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334838 prefixEnd_3334838 := by exact prefixLift 3334838
  have htrace : WordTrace (prefixWord ++ tailWord_3334838) baseStart_3334838 baseEnd_3334838 := by
    simpa [prefixWord, tailWord_3334838, baseEnd_3334838] using wordTrace_append hprefix tailTrace_3334838
  have hstable : (prefixWord ++ tailWord_3334838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334838).length < 2 ^ (prefixWord ++ tailWord_3334838).sum := by decide
  have hdescent : baseEnd_3334838 < baseStart_3334838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334866 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3334866 : Nat := 118140960795 + 3334866 * 2 ^ 59
def prefixEnd_3334866 : Nat := 4983230072969 + 3 ^ 40 * 3334866 * 2
def baseEnd_3334866 : Nat := 380530928074856567808497

theorem tailTrace_3334866 : CollatzResearch.WordTrace tailWord_3334866 prefixEnd_3334866 380530928074856567808497 := by
  unfold tailWord_3334866
  simp only [CollatzResearch.WordTrace]
  refine ⟨30408138884089376653434113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81088370357571671075824301 30408138884089376653434113)
  ·
    refine ⟨22806104163067032490075585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30408138884089376653434113 22806104163067032490075585)
    ·
      refine ⟨17104578122300274367556689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22806104163067032490075585 17104578122300274367556689)
      ·
        refine ⟨12828433591725205775667517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17104578122300274367556689 12828433591725205775667517)
        ·
          refine ⟨4810662596896952165875319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12828433591725205775667517 4810662596896952165875319)
          ·
            refine ⟨7215993895345428248812979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810662596896952165875319 7215993895345428248812979)
            ·
              refine ⟨10823990843018142373219469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215993895345428248812979 10823990843018142373219469)
              ·
                refine ⟨4058996566131803389957301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10823990843018142373219469 4058996566131803389957301)
                ·
                  refine ⟨380530928074856567808497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4058996566131803389957301 380530928074856567808497)
                  ·
                    rfl

theorem cell22_3334866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3334866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334866 prefixEnd_3334866 := by exact prefixLift 3334866
  have htrace : WordTrace (prefixWord ++ tailWord_3334866) baseStart_3334866 baseEnd_3334866 := by
    simpa [prefixWord, tailWord_3334866, baseEnd_3334866] using wordTrace_append hprefix tailTrace_3334866
  have hstable : (prefixWord ++ tailWord_3334866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334866).length < 2 ^ (prefixWord ++ tailWord_3334866).sum := by decide
  have hdescent : baseEnd_3334866 < baseStart_3334866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334879 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 3, 4]
def baseStart_3334879 : Nat := 118140960795 + 3334879 * 2 ^ 59
def prefixEnd_3334879 : Nat := 4983230072969 + 3 ^ 40 * 3334879 * 2
def baseEnd_3334879 : Nat := 1141597234390242002850451

theorem tailTrace_3334879 : CollatzResearch.WordTrace tailWord_3334879 prefixEnd_3334879 1141597234390242002850451 := by
  unfold tailWord_3334879
  simp only [CollatzResearch.WordTrace]
  refine ⟨121633029685310409833959691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81088686456873606555973127 121633029685310409833959691)
  ·
    refine ⟨182449544527965614750939537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121633029685310409833959691 182449544527965614750939537)
    ·
      refine ⟨136837158395974211063204653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182449544527965614750939537 136837158395974211063204653)
      ·
        refine ⟨51313934398490329148701745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136837158395974211063204653 51313934398490329148701745)
        ·
          refine ⟨38485450798867746861526309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51313934398490329148701745 38485450798867746861526309)
          ·
            refine ⟨7216022024787702536536183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38485450798867746861526309 7216022024787702536536183)
            ·
              refine ⟨10824033037181553804804275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216022024787702536536183 10824033037181553804804275)
              ·
                refine ⟨16236049555772330707206413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10824033037181553804804275 16236049555772330707206413)
                ·
                  refine ⟨6088518583414624015202405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16236049555772330707206413 6088518583414624015202405)
                  ·
                    refine ⟨1141597234390242002850451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088518583414624015202405 1141597234390242002850451)
                    ·
                      rfl

theorem cell22_3334879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_3334879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334879 prefixEnd_3334879 := by exact prefixLift 3334879
  have htrace : WordTrace (prefixWord ++ tailWord_3334879) baseStart_3334879 baseEnd_3334879 := by
    simpa [prefixWord, tailWord_3334879, baseEnd_3334879] using wordTrace_append hprefix tailTrace_3334879
  have hstable : (prefixWord ++ tailWord_3334879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334879).length < 2 ^ (prefixWord ++ tailWord_3334879).sum := by decide
  have hdescent : baseEnd_3334879 < baseStart_3334879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334896 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 1, 4]
def baseStart_3334896 : Nat := 118140960795 + 3334896 * 2 ^ 59
def prefixEnd_3334896 : Nat := 4983230072969 + 3 ^ 40 * 3334896 * 2
def baseEnd_3334896 : Nat := 1141603053837659625175399

theorem tailTrace_3334896 : CollatzResearch.WordTrace tailWord_3334896 prefixEnd_3334896 1141603053837659625175399 := by
  unfold tailWord_3334896
  simp only [CollatzResearch.WordTrace]
  refine ⟨60816824863124410868664271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81089099817499214491552361 60816824863124410868664271)
  ·
    refine ⟨91225237294686616302996407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60816824863124410868664271 91225237294686616302996407)
    ·
      refine ⟨136837855942029924454494611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91225237294686616302996407 136837855942029924454494611)
      ·
        refine ⟨205256783913044886681741917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136837855942029924454494611 205256783913044886681741917)
        ·
          refine ⟨76971293967391832505653219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205256783913044886681741917 76971293967391832505653219)
          ·
            refine ⟨115456940951087748758479829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76971293967391832505653219 115456940951087748758479829)
            ·
              refine ⟨2706022053541119111526871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 115456940951087748758479829 2706022053541119111526871)
              ·
                refine ⟨4059033080311678667290307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706022053541119111526871 4059033080311678667290307)
                ·
                  refine ⟨6088549620467518000935461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059033080311678667290307 6088549620467518000935461)
                  ·
                    refine ⟨1141603053837659625175399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088549620467518000935461 1141603053837659625175399)
                    ·
                      rfl

theorem cell22_3334896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_3334896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334896 prefixEnd_3334896 := by exact prefixLift 3334896
  have htrace : WordTrace (prefixWord ++ tailWord_3334896) baseStart_3334896 baseEnd_3334896 := by
    simpa [prefixWord, tailWord_3334896, baseEnd_3334896] using wordTrace_append hprefix tailTrace_3334896
  have hstable : (prefixWord ++ tailWord_3334896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334896).length < 2 ^ (prefixWord ++ tailWord_3334896).sum := by decide
  have hdescent : baseEnd_3334896 < baseStart_3334896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334900 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3334900 : Nat := 118140960795 + 3334900 * 2 ^ 59
def prefixEnd_3334900 : Nat := 4983230072969 + 3 ^ 40 * 3334900 * 2
def baseEnd_3334900 : Nat := 380534807706468316025129

theorem tailTrace_3334900 : CollatzResearch.WordTrace tailWord_3334900 prefixEnd_3334900 380534807706468316025129 := by
  unfold tailWord_3334900
  simp only [CollatzResearch.WordTrace]
  refine ⟨60816897809117165210237077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81089197078822886946982769 60816897809117165210237077)
  ·
    refine ⟨2850792084802367119229863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60816897809117165210237077 2850792084802367119229863)
    ·
      refine ⟨4276188127203550678844795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850792084802367119229863 4276188127203550678844795)
      ·
        refine ⟨6414282190805326018267193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276188127203550678844795 6414282190805326018267193)
        ·
          refine ⟨4810711643103994513700395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6414282190805326018267193 4810711643103994513700395)
          ·
            refine ⟨7216067464655991770550593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810711643103994513700395 7216067464655991770550593)
            ·
              refine ⟨5412050598491993827912945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216067464655991770550593 5412050598491993827912945)
              ·
                refine ⟨4059037948868995370934709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5412050598491993827912945 4059037948868995370934709)
                ·
                  refine ⟨380534807706468316025129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4059037948868995370934709 380534807706468316025129)
                  ·
                    rfl

theorem cell22_3334900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3334900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334900 prefixEnd_3334900 := by exact prefixLift 3334900
  have htrace : WordTrace (prefixWord ++ tailWord_3334900) baseStart_3334900 baseEnd_3334900 := by
    simpa [prefixWord, tailWord_3334900, baseEnd_3334900] using wordTrace_append hprefix tailTrace_3334900
  have hstable : (prefixWord ++ tailWord_3334900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334900).length < 2 ^ (prefixWord ++ tailWord_3334900).sum := by decide
  have hdescent : baseEnd_3334900 < baseStart_3334900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334937 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_3334937 : Nat := 118140960795 + 3334937 * 2 ^ 59
def prefixEnd_3334937 : Nat := 4983230072969 + 3 ^ 40 * 3334937 * 2
def baseEnd_3334937 : Nat := 1141617088975549184900273

theorem tailTrace_3334937 : CollatzResearch.WordTrace tailWord_3334937 prefixEnd_3334937 1141617088975549184900273 := by
  unfold tailWord_3334937
  simp only [CollatzResearch.WordTrace]
  refine ⟨121635145119100285739571065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81090096746066857159714043 121635145119100285739571065)
  ·
    refine ⟨91226358839325214304678299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121635145119100285739571065 91226358839325214304678299)
    ·
      refine ⟨136839538258987821457017449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91226358839325214304678299 136839538258987821457017449)
      ·
        refine ⟨102629653694240866092763087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136839538258987821457017449 102629653694240866092763087)
        ·
          refine ⟨153944480541361299139144631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102629653694240866092763087 153944480541361299139144631)
          ·
            refine ⟨230916720812041948708716947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153944480541361299139144631 230916720812041948708716947)
            ·
              refine ⟨346375081218062923063075421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230916720812041948708716947 346375081218062923063075421)
              ·
                refine ⟨129890655456773596148653283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346375081218062923063075421 129890655456773596148653283)
                ·
                  refine ⟨194835983185160394222979925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129890655456773596148653283 194835983185160394222979925)
                  ·
                    refine ⟨1141617088975549184900273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194835983185160394222979925 1141617088975549184900273)
                    ·
                      rfl

theorem cell22_3334937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_3334937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334937 prefixEnd_3334937 := by exact prefixLift 3334937
  have htrace : WordTrace (prefixWord ++ tailWord_3334937) baseStart_3334937 baseEnd_3334937 := by
    simpa [prefixWord, tailWord_3334937, baseEnd_3334937] using wordTrace_append hprefix tailTrace_3334937
  have hstable : (prefixWord ++ tailWord_3334937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334937).length < 2 ^ (prefixWord ++ tailWord_3334937).sum := by decide
  have hdescent : baseEnd_3334937 < baseStart_3334937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334977 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3334977 : Nat := 118140960795 + 3334977 * 2 ^ 59
def prefixEnd_3334977 : Nat := 4983230072969 + 3 ^ 40 * 3334977 * 2
def baseEnd_3334977 : Nat := 1141630781793002413900151

theorem tailTrace_3334977 : CollatzResearch.WordTrace tailWord_3334977 prefixEnd_3334977 1141630781793002413900151 := by
  unfold tailWord_3334977
  simp only [CollatzResearch.WordTrace]
  refine ⟨121636604038955372571027185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81091069359303581714018123 121636604038955372571027185)
  ·
    refine ⟨91227453029216529428270389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121636604038955372571027185 91227453029216529428270389)
    ·
      refine ⟨8552573721489049633900349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91227453029216529428270389 8552573721489049633900349)
      ·
        refine ⟨3207215145558393612712631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8552573721489049633900349 3207215145558393612712631)
        ·
          refine ⟨4810822718337590419068947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207215145558393612712631 4810822718337590419068947)
          ·
            refine ⟨7216234077506385628603421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810822718337590419068947 7216234077506385628603421)
            ·
              refine ⟨2706087779064894610726283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7216234077506385628603421 2706087779064894610726283)
              ·
                refine ⟨4059131668597341916089425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706087779064894610726283 4059131668597341916089425)
                ·
                  refine ⟨3044348751448006437067069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4059131668597341916089425 3044348751448006437067069)
                  ·
                    refine ⟨1141630781793002413900151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3044348751448006437067069 1141630781793002413900151)
                    ·
                      rfl

theorem cell22_3334977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3334977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334977 prefixEnd_3334977 := by exact prefixLift 3334977
  have htrace : WordTrace (prefixWord ++ tailWord_3334977) baseStart_3334977 baseEnd_3334977 := by
    simpa [prefixWord, tailWord_3334977, baseEnd_3334977] using wordTrace_append hprefix tailTrace_3334977
  have hstable : (prefixWord ++ tailWord_3334977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334977).length < 2 ^ (prefixWord ++ tailWord_3334977).sum := by decide
  have hdescent : baseEnd_3334977 < baseStart_3334977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335022 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3335022 : Nat := 118140960795 + 3335022 * 2 ^ 59
def prefixEnd_3335022 : Nat := 4983230072969 + 3 ^ 40 * 3335022 * 2
def baseEnd_3335022 : Nat := 1141646186212637296525013

theorem tailTrace_3335022 : CollatzResearch.WordTrace tailWord_3335022 prefixEnd_3335022 1141646186212637296525013 := by
  unfold tailWord_3335022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15204780665474043157051915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81092163549194896837610213 15204780665474043157051915)
  ·
    refine ⟨22807170998211064735577873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15204780665474043157051915 22807170998211064735577873)
    ·
      refine ⟨17105378248658298551683405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22807170998211064735577873 17105378248658298551683405)
      ·
        refine ⟨6414516843246861956881277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17105378248658298551683405 6414516843246861956881277)
        ·
          refine ⟨2405443816217573233830479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6414516843246861956881277 2405443816217573233830479)
          ·
            refine ⟨3608165724326359850745719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405443816217573233830479 3608165724326359850745719)
            ·
              refine ⟨5412248586489539776118579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3608165724326359850745719 5412248586489539776118579)
              ·
                refine ⟨8118372879734309664177869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412248586489539776118579 8118372879734309664177869)
                ·
                  refine ⟨3044389829900366124066701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8118372879734309664177869 3044389829900366124066701)
                  ·
                    refine ⟨1141646186212637296525013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3044389829900366124066701 1141646186212637296525013)
                    ·
                      rfl

theorem cell22_3335022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3335022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335022 prefixEnd_3335022 := by exact prefixLift 3335022
  have htrace : WordTrace (prefixWord ++ tailWord_3335022) baseStart_3335022 baseEnd_3335022 := by
    simpa [prefixWord, tailWord_3335022, baseEnd_3335022] using wordTrace_append hprefix tailTrace_3335022
  have hstable : (prefixWord ++ tailWord_3335022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335022).length < 2 ^ (prefixWord ++ tailWord_3335022).sum := by decide
  have hdescent : baseEnd_3335022 < baseStart_3335022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335048 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3335048 : Nat := 118140960795 + 3335048 * 2 ^ 59
def prefixEnd_3335048 : Nat := 4983230072969 + 3 ^ 40 * 3335048 * 2
def baseEnd_3335048 : Nat := 1141655086543981895374933

theorem tailTrace_3335048 : CollatzResearch.WordTrace tailWord_3335048 prefixEnd_3335048 1141655086543981895374933 := by
  unfold tailWord_3335048
  simp only [CollatzResearch.WordTrace]
  refine ⟨60819596810849075848430899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81092795747798767797907865 60819596810849075848430899)
  ·
    refine ⟨91229395216273613772646349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60819596810849075848430899 91229395216273613772646349)
    ·
      refine ⟨34211023206102605164742381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91229395216273613772646349 34211023206102605164742381)
      ·
        refine ⟨12829133702288476936778393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34211023206102605164742381 12829133702288476936778393)
        ·
          refine ⟨9621850276716357702583795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12829133702288476936778393 9621850276716357702583795)
          ·
            refine ⟨14432775415074536553875693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9621850276716357702583795 14432775415074536553875693)
            ·
              refine ⟨5412290780652951207703385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14432775415074536553875693 5412290780652951207703385)
              ·
                refine ⟨4059218085489713405777539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5412290780652951207703385 4059218085489713405777539)
                ·
                  refine ⟨6088827128234570108666309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059218085489713405777539 6088827128234570108666309)
                  ·
                    refine ⟨1141655086543981895374933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088827128234570108666309 1141655086543981895374933)
                    ·
                      rfl

theorem cell22_3335048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3335048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335048 prefixEnd_3335048 := by exact prefixLift 3335048
  have htrace : WordTrace (prefixWord ++ tailWord_3335048) baseStart_3335048 baseEnd_3335048 := by
    simpa [prefixWord, tailWord_3335048, baseEnd_3335048] using wordTrace_append hprefix tailTrace_3335048
  have hstable : (prefixWord ++ tailWord_3335048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335048).length < 2 ^ (prefixWord ++ tailWord_3335048).sum := by decide
  have hdescent : baseEnd_3335048 < baseStart_3335048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335061 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3335061 : Nat := 118140960795 + 3335061 * 2 ^ 59
def prefixEnd_3335061 : Nat := 4983230072969 + 3 ^ 40 * 3335061 * 2
def baseEnd_3335061 : Nat := 1141659536709654194799893

theorem tailTrace_3335061 : CollatzResearch.WordTrace tailWord_3335061 prefixEnd_3335061 1141659536709654194799893 := by
  unfold tailWord_3335061
  simp only [CollatzResearch.WordTrace]
  refine ⟨121639667770651054917085037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81093111847100703278056691 121639667770651054917085037)
  ·
    refine ⟨45614875413994145593906889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121639667770651054917085037 45614875413994145593906889)
    ·
      refine ⟨34211156560495609195430167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45614875413994145593906889 34211156560495609195430167)
      ·
        refine ⟨51316734840743413793145251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34211156560495609195430167 51316734840743413793145251)
        ·
          refine ⟨76975102261115120689717877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51316734840743413793145251 76975102261115120689717877)
          ·
            refine ⟨7216415836979542564661051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76975102261115120689717877 7216415836979542564661051)
            ·
              refine ⟨10824623755469313846991577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216415836979542564661051 10824623755469313846991577)
              ·
                refine ⟨8118467816601985385243683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10824623755469313846991577 8118467816601985385243683)
                ·
                  refine ⟨12177701724902978077865525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118467816601985385243683 12177701724902978077865525)
                  ·
                    refine ⟨1141659536709654194799893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12177701724902978077865525 1141659536709654194799893)
                    ·
                      rfl

theorem cell22_3335061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3335061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335061 prefixEnd_3335061 := by exact prefixLift 3335061
  have htrace : WordTrace (prefixWord ++ tailWord_3335061) baseStart_3335061 baseEnd_3335061 := by
    simpa [prefixWord, tailWord_3335061, baseEnd_3335061] using wordTrace_append hprefix tailTrace_3335061
  have hstable : (prefixWord ++ tailWord_3335061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335061).length < 2 ^ (prefixWord ++ tailWord_3335061).sum := by decide
  have hdescent : baseEnd_3335061 < baseStart_3335061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335076 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_3335076 : Nat := 118140960795 + 3335076 * 2 ^ 59
def prefixEnd_3335076 : Nat := 4983230072969 + 3 ^ 40 * 3335076 * 2
def baseEnd_3335076 : Nat := 1141664671516199155674847

theorem tailTrace_3335076 : CollatzResearch.WordTrace tailWord_3335076 prefixEnd_3335076 1141664671516199155674847 := by
  unfold tailWord_3335076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60820107432798356239440541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81093476577064474985920721 60820107432798356239440541)
  ·
    refine ⟨22807540287299383589790203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60820107432798356239440541 22807540287299383589790203)
    ·
      refine ⟨34211310430949075384685305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22807540287299383589790203 34211310430949075384685305)
      ·
        refine ⟨25658482823211806538513979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34211310430949075384685305 25658482823211806538513979)
        ·
          refine ⟨38487724234817709807770969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25658482823211806538513979 38487724234817709807770969)
          ·
            refine ⟨28865793176113282355828227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38487724234817709807770969 28865793176113282355828227)
            ·
              refine ⟨43298689764169923533742341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28865793176113282355828227 43298689764169923533742341)
              ·
                refine ⟨8118504330781860662576689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43298689764169923533742341 8118504330781860662576689)
                ·
                  refine ⟨6088878248086395496932517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118504330781860662576689 6088878248086395496932517)
                  ·
                    refine ⟨1141664671516199155674847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088878248086395496932517 1141664671516199155674847)
                    ·
                      rfl

theorem cell22_3335076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_3335076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335076 prefixEnd_3335076 := by exact prefixLift 3335076
  have htrace : WordTrace (prefixWord ++ tailWord_3335076) baseStart_3335076 baseEnd_3335076 := by
    simpa [prefixWord, tailWord_3335076, baseEnd_3335076] using wordTrace_append hprefix tailTrace_3335076
  have hstable : (prefixWord ++ tailWord_3335076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335076).length < 2 ^ (prefixWord ++ tailWord_3335076).sum := by decide
  have hdescent : baseEnd_3335076 < baseStart_3335076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335151 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 2, 5]
def baseStart_3335151 : Nat := 118140960795 + 3335151 * 2 ^ 59
def prefixEnd_3335151 : Nat := 4983230072969 + 3 ^ 40 * 3335151 * 2
def baseEnd_3335151 : Nat := 1141690345548923960049617

theorem tailTrace_3335151 : CollatzResearch.WordTrace tailWord_3335151 prefixEnd_3335151 1141690345548923960049617 := by
  unfold tailWord_3335151
  simp only [CollatzResearch.WordTrace]
  refine ⟨121642950340325000287861307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81095300226883333525240871 121642950340325000287861307)
  ·
    refine ⟨182464425510487500431791961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121642950340325000287861307 182464425510487500431791961)
    ·
      refine ⟨136848319132865625323843971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182464425510487500431791961 136848319132865625323843971)
      ·
        refine ⟨205272478699298437985765957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136848319132865625323843971 205272478699298437985765957)
        ·
          refine ⟨38488589756118457122331117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205272478699298437985765957 38488589756118457122331117)
          ·
            refine ⟨14433221158544421420874169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38488589756118457122331117 14433221158544421420874169)
            ·
              refine ⟨10824915868908316065655627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14433221158544421420874169 10824915868908316065655627)
              ·
                refine ⟨16237373803362474098483441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10824915868908316065655627 16237373803362474098483441)
                ·
                  refine ⟨12178030352521855573862581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16237373803362474098483441 12178030352521855573862581)
                  ·
                    refine ⟨1141690345548923960049617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12178030352521855573862581 1141690345548923960049617)
                    ·
                      rfl

theorem cell22_3335151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_3335151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335151 prefixEnd_3335151 := by exact prefixLift 3335151
  have htrace : WordTrace (prefixWord ++ tailWord_3335151) baseStart_3335151 baseEnd_3335151 := by
    simpa [prefixWord, tailWord_3335151, baseEnd_3335151] using wordTrace_append hprefix tailTrace_3335151
  have hstable : (prefixWord ++ tailWord_3335151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335151).length < 2 ^ (prefixWord ++ tailWord_3335151).sum := by decide
  have hdescent : baseEnd_3335151 < baseStart_3335151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335211 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 4, 4]
def baseStart_3335211 : Nat := 118140960795 + 3335211 * 2 ^ 59
def prefixEnd_3335211 : Nat := 4983230072969 + 3 ^ 40 * 3335211 * 2
def baseEnd_3335211 : Nat := 1141710884775103803549433

theorem tailTrace_3335211 : CollatzResearch.WordTrace tailWord_3335211 prefixEnd_3335211 1141710884775103803549433 := by
  unfold tailWord_3335211
  simp only [CollatzResearch.WordTrace]
  refine ⟨121645138720107630535045487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81096759146738420356696991 121645138720107630535045487)
  ·
    refine ⟨182467708080161445802568231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121645138720107630535045487 182467708080161445802568231)
    ·
      refine ⟨273701562120242168703852347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182467708080161445802568231 273701562120242168703852347)
      ·
        refine ⟨410552343180363253055778521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273701562120242168703852347 410552343180363253055778521)
        ·
          refine ⟨307914257385272439791833891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410552343180363253055778521 307914257385272439791833891)
          ·
            refine ⟨461871386077908659687750837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307914257385272439791833891 461871386077908659687750837)
            ·
              refine ⟨43300442444803936845726641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 461871386077908659687750837 43300442444803936845726641)
              ·
                refine ⟨32475331833602952634294981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43300442444803936845726641 32475331833602952634294981)
                ·
                  refine ⟨6089124718800553618930309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32475331833602952634294981 6089124718800553618930309)
                  ·
                    refine ⟨1141710884775103803549433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6089124718800553618930309 1141710884775103803549433)
                    ·
                      rfl

theorem cell22_3335211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_3335211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335211 prefixEnd_3335211 := by exact prefixLift 3335211
  have htrace : WordTrace (prefixWord ++ tailWord_3335211) baseStart_3335211 baseEnd_3335211 := by
    simpa [prefixWord, tailWord_3335211, baseEnd_3335211] using wordTrace_append hprefix tailTrace_3335211
  have hstable : (prefixWord ++ tailWord_3335211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335211).length < 2 ^ (prefixWord ++ tailWord_3335211).sum := by decide
  have hdescent : baseEnd_3335211 < baseStart_3335211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335226 : List Nat := [3, 1, 1, 1, 3, 1, 4, 8]
def baseStart_3335226 : Nat := 118140960795 + 3335226 * 2 ^ 59
def prefixEnd_3335226 : Nat := 4983230072969 + 3 ^ 40 * 3335226 * 2
def baseEnd_3335226 : Nat := 126857335509072084936043

theorem tailTrace_3335226 : CollatzResearch.WordTrace tailWord_3335226 prefixEnd_3335226 126857335509072084936043 := by
  unfold tailWord_3335226
  simp only [CollatzResearch.WordTrace]
  refine ⟨30411421453763322024210383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81097123876702192064561021 30411421453763322024210383)
  ·
    refine ⟨45617132180644983036315575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30411421453763322024210383 45617132180644983036315575)
    ·
      refine ⟨68425698270967474554473363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45617132180644983036315575 68425698270967474554473363)
      ·
        refine ⟨102638547406451211831710045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68425698270967474554473363 102638547406451211831710045)
        ·
          refine ⟨38489455277419204436891267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102638547406451211831710045 38489455277419204436891267)
          ·
            refine ⟨57734182916128806655336901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38489455277419204436891267 57734182916128806655336901)
            ·
              refine ⟨10825159296774151247875669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57734182916128806655336901 10825159296774151247875669)
              ·
                refine ⟨126857335509072084936043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10825159296774151247875669 126857335509072084936043)
                ·
                  rfl

theorem cell22_3335226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_3335226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335226 prefixEnd_3335226 := by exact prefixLift 3335226
  have htrace : WordTrace (prefixWord ++ tailWord_3335226) baseStart_3335226 baseEnd_3335226 := by
    simpa [prefixWord, tailWord_3335226, baseEnd_3335226] using wordTrace_append hprefix tailTrace_3335226
  have hstable : (prefixWord ++ tailWord_3335226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335226).length < 2 ^ (prefixWord ++ tailWord_3335226).sum := by decide
  have hdescent : baseEnd_3335226 < baseStart_3335226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335228 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3335228 : Nat := 118140960795 + 3335228 * 2 ^ 59
def prefixEnd_3335228 : Nat := 4983230072969 + 3 ^ 40 * 3335228 * 2
def baseEnd_3335228 : Nat := 1141716704222521425874381

theorem tailTrace_3335228 : CollatzResearch.WordTrace tailWord_3335228 prefixEnd_3335228 1141716704222521425874381 := by
  unfold tailWord_3335228
  simp only [CollatzResearch.WordTrace]
  refine ⟨60822879380523021219207169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81097172507364028292276225 60822879380523021219207169)
  ·
    refine ⟨45617159535392265914405377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60822879380523021219207169 45617159535392265914405377)
    ·
      refine ⟨34212869651544199435804033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45617159535392265914405377 34212869651544199435804033)
      ·
        refine ⟨25659652238658149576853025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34212869651544199435804033 25659652238658149576853025)
        ·
          refine ⟨19244739178993612182639769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25659652238658149576853025 19244739178993612182639769)
          ·
            refine ⟨14433554384245209136979827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19244739178993612182639769 14433554384245209136979827)
            ·
              refine ⟨21650331576367813705469741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14433554384245209136979827 21650331576367813705469741)
              ·
                refine ⟨8118874341137930139551153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21650331576367813705469741 8118874341137930139551153)
                ·
                  refine ⟨6089155755853447604663365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118874341137930139551153 6089155755853447604663365)
                  ·
                    refine ⟨1141716704222521425874381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6089155755853447604663365 1141716704222521425874381)
                    ·
                      rfl

theorem cell22_3335228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3335228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335228 prefixEnd_3335228 := by exact prefixLift 3335228
  have htrace : WordTrace (prefixWord ++ tailWord_3335228) baseStart_3335228 baseEnd_3335228 := by
    simpa [prefixWord, tailWord_3335228, baseEnd_3335228] using wordTrace_append hprefix tailTrace_3335228
  have hstable : (prefixWord ++ tailWord_3335228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335228).length < 2 ^ (prefixWord ++ tailWord_3335228).sum := by decide
  have hdescent : baseEnd_3335228 < baseStart_3335228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335230 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3335230 : Nat := 118140960795 + 3335230 * 2 ^ 59
def prefixEnd_3335230 : Nat := 4983230072969 + 3 ^ 40 * 3335230 * 2
def baseEnd_3335230 : Nat := 1141717388863394087324375

theorem tailTrace_3335230 : CollatzResearch.WordTrace tailWord_3335230 prefixEnd_3335230 1141717388863394087324375 := by
  unfold tailWord_3335230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205728963379849597498393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81097221138025864519991429 15205728963379849597498393)
  ·
    refine ⟨11404296722534887198123795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15205728963379849597498393 11404296722534887198123795)
    ·
      refine ⟨17106445083802330797185693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11404296722534887198123795 17106445083802330797185693)
      ·
        refine ⟨6414916906425874048944635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17106445083802330797185693 6414916906425874048944635)
        ·
          refine ⟨9622375359638811073416953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414916906425874048944635 9622375359638811073416953)
          ·
            refine ⟨7216781519729108305062715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622375359638811073416953 7216781519729108305062715)
            ·
              refine ⟨10825172279593662457594073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216781519729108305062715 10825172279593662457594073)
              ·
                refine ⟨8118879209695246843195555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10825172279593662457594073 8118879209695246843195555)
                ·
                  refine ⟨12178318814542870264793333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118879209695246843195555 12178318814542870264793333)
                  ·
                    refine ⟨1141717388863394087324375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12178318814542870264793333 1141717388863394087324375)
                    ·
                      rfl

theorem cell22_3335230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3335230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335230 prefixEnd_3335230 := by exact prefixLift 3335230
  have htrace : WordTrace (prefixWord ++ tailWord_3335230) baseStart_3335230 baseEnd_3335230 := by
    simpa [prefixWord, tailWord_3335230, baseEnd_3335230] using wordTrace_append hprefix tailTrace_3335230
  have hstable : (prefixWord ++ tailWord_3335230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335230).length < 2 ^ (prefixWord ++ tailWord_3335230).sum := by decide
  have hdescent : baseEnd_3335230 < baseStart_3335230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335245 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3335245 : Nat := 118140960795 + 3335245 * 2 ^ 59
def prefixEnd_3335245 : Nat := 4983230072969 + 3 ^ 40 * 3335245 * 2
def baseEnd_3335245 : Nat := 1141722523669939048199329

theorem tailTrace_3335245 : CollatzResearch.WordTrace tailWord_3335245 prefixEnd_3335245 1141722523669939048199329 := by
  unfold tailWord_3335245
  simp only [CollatzResearch.WordTrace]
  refine ⟨121646378801984454341783189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81097585867989636227855459 121646378801984454341783189)
  ·
    refine ⟨5702174006343021297271087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121646378801984454341783189 5702174006343021297271087)
    ·
      refine ⟨8553261009514531945906631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5702174006343021297271087 8553261009514531945906631)
      ·
        refine ⟨12829891514271797918859947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8553261009514531945906631 12829891514271797918859947)
        ·
          refine ⟨19244837271407696878289921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12829891514271797918859947 19244837271407696878289921)
          ·
            refine ⟨14433627953555772658717441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19244837271407696878289921 14433627953555772658717441)
            ·
              refine ⟨10825220965166829494038081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14433627953555772658717441 10825220965166829494038081)
              ·
                refine ⟨8118915723875122120528561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10825220965166829494038081 8118915723875122120528561)
                ·
                  refine ⟨6089186792906341590396421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118915723875122120528561 6089186792906341590396421)
                  ·
                    refine ⟨1141722523669939048199329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6089186792906341590396421 1141722523669939048199329)
                    ·
                      rfl

theorem cell22_3335245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3335245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335245 prefixEnd_3335245 := by exact prefixLift 3335245
  have htrace : WordTrace (prefixWord ++ tailWord_3335245) baseStart_3335245 baseEnd_3335245 := by
    simpa [prefixWord, tailWord_3335245, baseEnd_3335245] using wordTrace_append hprefix tailTrace_3335245
  have hstable : (prefixWord ++ tailWord_3335245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335245).length < 2 ^ (prefixWord ++ tailWord_3335245).sum := by decide
  have hdescent : baseEnd_3335245 < baseStart_3335245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335256 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_3335256 : Nat := 118140960795 + 3335256 * 2 ^ 59
def prefixEnd_3335256 : Nat := 4983230072969 + 3 ^ 40 * 3335256 * 2
def baseEnd_3335256 : Nat := 1141726289194738686174295

theorem tailTrace_3335256 : CollatzResearch.WordTrace tailWord_3335256 prefixEnd_3335256 1141726289194738686174295 := by
  unfold tailWord_3335256
  simp only [CollatzResearch.WordTrace]
  refine ⟨60823390002472301610216811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81097853336629735480289081 60823390002472301610216811)
  ·
    refine ⟨91235085003708452415325217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60823390002472301610216811 91235085003708452415325217)
    ·
      refine ⟨68426313752781339311493913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91235085003708452415325217 68426313752781339311493913)
      ·
        refine ⟨51319735314586004483620435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68426313752781339311493913 51319735314586004483620435)
        ·
          refine ⟨76979602971879006725430653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51319735314586004483620435 76979602971879006725430653)
          ·
            refine ⟨28867351114454627522036495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76979602971879006725430653 28867351114454627522036495)
            ·
              refine ⟨43301026671681941283054743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28867351114454627522036495 43301026671681941283054743)
              ·
                refine ⟨64951540007522911924582115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43301026671681941283054743 64951540007522911924582115)
                ·
                  refine ⟨97427310011284367886873173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64951540007522911924582115 97427310011284367886873173)
                  ·
                    refine ⟨1141726289194738686174295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97427310011284367886873173 1141726289194738686174295)
                    ·
                      rfl

theorem cell22_3335256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_3335256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335256 prefixEnd_3335256 := by exact prefixLift 3335256
  have htrace : WordTrace (prefixWord ++ tailWord_3335256) baseStart_3335256 baseEnd_3335256 := by
    simpa [prefixWord, tailWord_3335256, baseEnd_3335256] using wordTrace_append hprefix tailTrace_3335256
  have hstable : (prefixWord ++ tailWord_3335256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335256).length < 2 ^ (prefixWord ++ tailWord_3335256).sum := by decide
  have hdescent : baseEnd_3335256 < baseStart_3335256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335292 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_3335292 : Nat := 118140960795 + 3335292 * 2 ^ 59
def prefixEnd_3335292 : Nat := 4983230072969 + 3 ^ 40 * 3335292 * 2
def baseEnd_3335292 : Nat := 1141738612730446592274185

theorem tailTrace_3335292 : CollatzResearch.WordTrace tailWord_3335292 prefixEnd_3335292 1141738612730446592274185 := by
  unfold tailWord_3335292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60824046516407090684372065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81098728688542787579162753 60824046516407090684372065)
  ·
    refine ⟨45618034887305318013279049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60824046516407090684372065 45618034887305318013279049)
    ·
      refine ⟨34213526165478988509959287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45618034887305318013279049 34213526165478988509959287)
      ·
        refine ⟨51320289248218482764938931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34213526165478988509959287 51320289248218482764938931)
        ·
          refine ⟨76980433872327724147408397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51320289248218482764938931 76980433872327724147408397)
          ·
            refine ⟨28867662702122896555278149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76980433872327724147408397 28867662702122896555278149)
            ·
              refine ⟨5412686756648043104114653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28867662702122896555278149 5412686756648043104114653)
              ·
                refine ⟨2029757533743016164042995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5412686756648043104114653 2029757533743016164042995)
                ·
                  refine ⟨3044636300614524246064493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029757533743016164042995 3044636300614524246064493)
                  ·
                    refine ⟨1141738612730446592274185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3044636300614524246064493 1141738612730446592274185)
                    ·
                      rfl

theorem cell22_3335292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_3335292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335292 prefixEnd_3335292 := by exact prefixLift 3335292
  have htrace : WordTrace (prefixWord ++ tailWord_3335292) baseStart_3335292 baseEnd_3335292 := by
    simpa [prefixWord, tailWord_3335292, baseEnd_3335292] using wordTrace_append hprefix tailTrace_3335292
  have hstable : (prefixWord ++ tailWord_3335292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335292).length < 2 ^ (prefixWord ++ tailWord_3335292).sum := by decide
  have hdescent : baseEnd_3335292 < baseStart_3335292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335305 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 5]
def baseStart_3335305 : Nat := 118140960795 + 3335305 * 2 ^ 59
def prefixEnd_3335305 : Nat := 4983230072969 + 3 ^ 40 * 3335305 * 2
def baseEnd_3335305 : Nat := 380581020965372963899715

theorem tailTrace_3335305 : CollatzResearch.WordTrace tailWord_3335305 prefixEnd_3335305 380581020965372963899715 := by
  unfold tailWord_3335305
  simp only [CollatzResearch.WordTrace]
  refine ⟨121648567181767084588967369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81099044787844723059311579 121648567181767084588967369)
  ·
    refine ⟨91236425386325313441725527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121648567181767084588967369 91236425386325313441725527)
    ·
      refine ⟨136854638079487970162588291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91236425386325313441725527 136854638079487970162588291)
      ·
        refine ⟨205281957119231955243882437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136854638079487970162588291 205281957119231955243882437)
        ·
          refine ⟨38490366959855991608227957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205281957119231955243882437 38490366959855991608227957)
          ·
            refine ⟨3608471902486499213271371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38490366959855991608227957 3608471902486499213271371)
            ·
              refine ⟨5412707853729748819907057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3608471902486499213271371 5412707853729748819907057)
              ·
                refine ⟨4059530890297311614930293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5412707853729748819907057 4059530890297311614930293)
                ·
                  refine ⟨380581020965372963899715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4059530890297311614930293 380581020965372963899715)
                  ·
                    rfl

theorem cell22_3335305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_3335305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335305 prefixEnd_3335305 := by exact prefixLift 3335305
  have htrace : WordTrace (prefixWord ++ tailWord_3335305) baseStart_3335305 baseEnd_3335305 := by
    simpa [prefixWord, tailWord_3335305, baseEnd_3335305] using wordTrace_append hprefix tailTrace_3335305
  have hstable : (prefixWord ++ tailWord_3335305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335305).length < 2 ^ (prefixWord ++ tailWord_3335305).sum := by decide
  have hdescent : baseEnd_3335305 < baseStart_3335305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335322 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_3335322 : Nat := 118140960795 + 3335322 * 2 ^ 59
def prefixEnd_3335322 : Nat := 4983230072969 + 3 ^ 40 * 3335322 * 2
def baseEnd_3335322 : Nat := 380582960781178838008031

theorem tailTrace_3335322 : CollatzResearch.WordTrace tailWord_3335322 prefixEnd_3335322 380582960781178838008031 := by
  unfold tailWord_3335322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412296805676374123084055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81099458148470330994890813 30412296805676374123084055)
  ·
    refine ⟨45618445208514561184626083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30412296805676374123084055 45618445208514561184626083)
    ·
      refine ⟨68427667812771841776939125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45618445208514561184626083 68427667812771841776939125)
      ·
        refine ⟨6415093857447360166588043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68427667812771841776939125 6415093857447360166588043)
        ·
          refine ⟨9622640786171040249882065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415093857447360166588043 9622640786171040249882065)
          ·
            refine ⟨7216980589628280187411549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622640786171040249882065 7216980589628280187411549)
            ·
              refine ⟨2706367721110605070279331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7216980589628280187411549 2706367721110605070279331)
              ·
                refine ⟨4059551581665907605418997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706367721110605070279331 4059551581665907605418997)
                ·
                  refine ⟨380582960781178838008031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4059551581665907605418997 380582960781178838008031)
                  ·
                    rfl

theorem cell22_3335322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_3335322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335322 prefixEnd_3335322 := by exact prefixLift 3335322
  have htrace : WordTrace (prefixWord ++ tailWord_3335322) baseStart_3335322 baseEnd_3335322 := by
    simpa [prefixWord, tailWord_3335322, baseEnd_3335322] using wordTrace_append hprefix tailTrace_3335322
  have hstable : (prefixWord ++ tailWord_3335322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335322).length < 2 ^ (prefixWord ++ tailWord_3335322).sum := by decide
  have hdescent : baseEnd_3335322 < baseStart_3335322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335333 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 6]
def baseStart_3335333 : Nat := 118140960795 + 3335333 * 2 ^ 59
def prefixEnd_3335333 : Nat := 4983230072969 + 3 ^ 40 * 3335333 * 2
def baseEnd_3335333 : Nat := 380584215956112050666353

theorem tailTrace_3335333 : CollatzResearch.WordTrace tailWord_3335333 prefixEnd_3335333 380584215956112050666353 := by
  unfold tailWord_3335333
  simp only [CollatzResearch.WordTrace]
  refine ⟨121649588425665645370986653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81099725617110430247324435 121649588425665645370986653)
  ·
    refine ⟨45618595659624617014119995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121649588425665645370986653 45618595659624617014119995)
    ·
      refine ⟨68427893489436925521179993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45618595659624617014119995 68427893489436925521179993)
      ·
        refine ⟨51320920117077694140884995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68427893489436925521179993 51320920117077694140884995)
        ·
          refine ⟨76981380175616541211327493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51320920117077694140884995 76981380175616541211327493)
          ·
            refine ⟨14434008782928101477123905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76981380175616541211327493 14434008782928101477123905)
            ·
              refine ⟨10825506587196076107842929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14434008782928101477123905 10825506587196076107842929)
              ·
                refine ⟨8119129940397057080882197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10825506587196076107842929 8119129940397057080882197)
                ·
                  refine ⟨380584215956112050666353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8119129940397057080882197 380584215956112050666353)
                  ·
                    rfl

theorem cell22_3335333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_3335333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335333 prefixEnd_3335333 := by exact prefixLift 3335333
  have htrace : WordTrace (prefixWord ++ tailWord_3335333) baseStart_3335333 baseEnd_3335333 := by
    simpa [prefixWord, tailWord_3335333, baseEnd_3335333] using wordTrace_append hprefix tailTrace_3335333
  have hstable : (prefixWord ++ tailWord_3335333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335333).length < 2 ^ (prefixWord ++ tailWord_3335333).sum := by decide
  have hdescent : baseEnd_3335333 < baseStart_3335333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335365 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_3335365 : Nat := 118140960795 + 3335365 * 2 ^ 59
def prefixEnd_3335365 : Nat := 4983230072969 + 3 ^ 40 * 3335365 * 2
def baseEnd_3335365 : Nat := 1141763602122298735198961

theorem tailTrace_3335365 : CollatzResearch.WordTrace tailWord_3335365 prefixEnd_3335365 1141763602122298735198961 := by
  unfold tailWord_3335365
  simp only [CollatzResearch.WordTrace]
  refine ⟨121650755561549714836151549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81100503707699809890767699 121650755561549714836151549)
  ·
    refine ⟨45619033335581143063556831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121650755561549714836151549 45619033335581143063556831)
    ·
      refine ⟨68428550003371714595335247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45619033335581143063556831 68428550003371714595335247)
      ·
        refine ⟨102642825005057571893002871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68428550003371714595335247 102642825005057571893002871)
        ·
          refine ⟨153964237507586357839504307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102642825005057571893002871 153964237507586357839504307)
          ·
            refine ⟨230946356261379536759256461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153964237507586357839504307 230946356261379536759256461)
            ·
              refine ⟨86604883598017326284721173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230946356261379536759256461 86604883598017326284721173)
              ·
                refine ⟨4059603918657062169596305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86604883598017326284721173 4059603918657062169596305)
                ·
                  refine ⟨3044702938992796627197229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4059603918657062169596305 3044702938992796627197229)
                  ·
                    refine ⟨1141763602122298735198961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3044702938992796627197229 1141763602122298735198961)
                    ·
                      rfl

theorem cell22_3335365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_3335365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335365 prefixEnd_3335365 := by exact prefixLift 3335365
  have htrace : WordTrace (prefixWord ++ tailWord_3335365) baseStart_3335365 baseEnd_3335365 := by
    simpa [prefixWord, tailWord_3335365, baseEnd_3335365] using wordTrace_append hprefix tailTrace_3335365
  have hstable : (prefixWord ++ tailWord_3335365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335365).length < 2 ^ (prefixWord ++ tailWord_3335365).sum := by decide
  have hdescent : baseEnd_3335365 < baseStart_3335365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335373 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3335373 : Nat := 118140960795 + 3335373 * 2 ^ 59
def prefixEnd_3335373 : Nat := 4983230072969 + 3 ^ 40 * 3335373 * 2
def baseEnd_3335373 : Nat := 380588780228596460332979

theorem tailTrace_3335373 : CollatzResearch.WordTrace tailWord_3335373 prefixEnd_3335373 380588780228596460332979 := by
  unfold tailWord_3335373
  simp only [CollatzResearch.WordTrace]
  refine ⟨121651047345520732202442773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81100698230347154801628515 121651047345520732202442773)
  ·
    refine ⟨5702392844321284321989505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121651047345520732202442773 5702392844321284321989505)
    ·
      refine ⟨4276794633240963241492129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5702392844321284321989505 4276794633240963241492129)
      ·
        refine ⟨3207595974930722431119097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4276794633240963241492129 3207595974930722431119097)
        ·
          refine ⟨2405696981198041823339323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3207595974930722431119097 2405696981198041823339323)
          ·
            refine ⟨3608545471797062735008985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405696981198041823339323 3608545471797062735008985)
            ·
              refine ⟨2706409103847797051256739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608545471797062735008985 2706409103847797051256739)
              ·
                refine ⟨4059613655771695576885109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706409103847797051256739 4059613655771695576885109)
                ·
                  refine ⟨380588780228596460332979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4059613655771695576885109 380588780228596460332979)
                  ·
                    rfl

theorem cell22_3335373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3335373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335373 prefixEnd_3335373 := by exact prefixLift 3335373
  have htrace : WordTrace (prefixWord ++ tailWord_3335373) baseStart_3335373 baseEnd_3335373 := by
    simpa [prefixWord, tailWord_3335373, baseEnd_3335373] using wordTrace_append hprefix tailTrace_3335373
  have hstable : (prefixWord ++ tailWord_3335373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335373).length < 2 ^ (prefixWord ++ tailWord_3335373).sum := by decide
  have hdescent : baseEnd_3335373 < baseStart_3335373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335397 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3335397 : Nat := 118140960795 + 3335397 * 2 ^ 59
def prefixEnd_3335397 : Nat := 4983230072969 + 3 ^ 40 * 3335397 * 2
def baseEnd_3335397 : Nat := 1141774556376261318398863

theorem tailTrace_3335397 : CollatzResearch.WordTrace tailWord_3335397 prefixEnd_3335397 1141774556376261318398863 := by
  unfold tailWord_3335397
  simp only [CollatzResearch.WordTrace]
  refine ⟨121651922697433784301316445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81101281798289189534210963 121651922697433784301316445)
  ·
    refine ⟨45619471011537669112993667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121651922697433784301316445 45619471011537669112993667)
    ·
      refine ⟨68429206517306503669490501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45619471011537669112993667 68429206517306503669490501)
      ·
        refine ⟨12830476221994969438029469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68429206517306503669490501 12830476221994969438029469)
        ·
          refine ⟨4811428583248113539261051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12830476221994969438029469 4811428583248113539261051)
          ·
            refine ⟨7217142874872170308891577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811428583248113539261051 7217142874872170308891577)
            ·
              refine ⟨5412857156154127731668683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7217142874872170308891577 5412857156154127731668683)
              ·
                refine ⟨8119285734231191597503025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412857156154127731668683 8119285734231191597503025)
                ·
                  refine ⟨6089464300673393698127269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8119285734231191597503025 6089464300673393698127269)
                  ·
                    refine ⟨1141774556376261318398863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6089464300673393698127269 1141774556376261318398863)
                    ·
                      rfl

theorem cell22_3335397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3335397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335397 prefixEnd_3335397 := by exact prefixLift 3335397
  have htrace : WordTrace (prefixWord ++ tailWord_3335397) baseStart_3335397 baseEnd_3335397 := by
    simpa [prefixWord, tailWord_3335397, baseEnd_3335397] using wordTrace_append hprefix tailTrace_3335397
  have hstable : (prefixWord ++ tailWord_3335397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335397).length < 2 ^ (prefixWord ++ tailWord_3335397).sum := by decide
  have hdescent : baseEnd_3335397 < baseStart_3335397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335412 : List Nat := [2, 6, 1, 2, 11]
def baseStart_3335412 : Nat := 118140960795 + 3335412 * 2 ^ 59
def prefixEnd_3335412 : Nat := 4983230072969 + 3 ^ 40 * 3335412 * 2
def baseEnd_3335412 : Nat := 4698681856719367404419

theorem tailTrace_3335412 : CollatzResearch.WordTrace tailWord_3335412 prefixEnd_3335412 4698681856719367404419 := by
  unfold tailWord_3335412
  simp only [CollatzResearch.WordTrace]
  refine ⟨60826234896189720931556245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81101646528252961242074993 60826234896189720931556245)
  ·
    refine ⟨2851229760758893168666699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60826234896189720931556245 2851229760758893168666699)
    ·
      refine ⟨4276844641138339753000049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851229760758893168666699 4276844641138339753000049)
      ·
        refine ⟨3207633480853754814750037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4276844641138339753000049 3207633480853754814750037)
        ·
          refine ⟨4698681856719367404419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3207633480853754814750037 4698681856719367404419)
          ·
            rfl

theorem cell22_3335412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 11].length) (baseStart_3335412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335412 prefixEnd_3335412 := by exact prefixLift 3335412
  have htrace : WordTrace (prefixWord ++ tailWord_3335412) baseStart_3335412 baseEnd_3335412 := by
    simpa [prefixWord, tailWord_3335412, baseEnd_3335412] using wordTrace_append hprefix tailTrace_3335412
  have hstable : (prefixWord ++ tailWord_3335412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335412).length < 2 ^ (prefixWord ++ tailWord_3335412).sum := by decide
  have hdescent : baseEnd_3335412 < baseStart_3335412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335468 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_3335468 : Nat := 118140960795 + 3335468 * 2 ^ 59
def prefixEnd_3335468 : Nat := 4983230072969 + 3 ^ 40 * 3335468 * 2
def baseEnd_3335468 : Nat := 380599620375746933291215

theorem tailTrace_3335468 : CollatzResearch.WordTrace tailWord_3335468 prefixEnd_3335468 380599620375746933291215 := by
  unfold tailWord_3335468
  simp only [CollatzResearch.WordTrace]
  refine ⟨60827256140088281713575529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81103008186784375618100705 60827256140088281713575529)
  ·
    refine ⟨45620442105066211285181647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60827256140088281713575529 45620442105066211285181647)
    ·
      refine ⟨68430663157599316927772471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45620442105066211285181647 68430663157599316927772471)
      ·
        refine ⟨102645994736398975391658707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68430663157599316927772471 102645994736398975391658707)
        ·
          refine ⟨153968992104598463087488061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102645994736398975391658707 153968992104598463087488061)
          ·
            refine ⟨57738372039224423657808023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153968992104598463087488061 57738372039224423657808023)
            ·
              refine ⟨86607558058836635486712035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57738372039224423657808023 86607558058836635486712035)
              ·
                refine ⟨129911337088254953230068053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86607558058836635486712035 129911337088254953230068053)
                ·
                  refine ⟨380599620375746933291215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129911337088254953230068053 380599620375746933291215)
                  ·
                    rfl

theorem cell22_3335468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_3335468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335468 prefixEnd_3335468 := by exact prefixLift 3335468
  have htrace : WordTrace (prefixWord ++ tailWord_3335468) baseStart_3335468 baseEnd_3335468 := by
    simpa [prefixWord, tailWord_3335468, baseEnd_3335468] using wordTrace_append hprefix tailTrace_3335468
  have hstable : (prefixWord ++ tailWord_3335468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335468).length < 2 ^ (prefixWord ++ tailWord_3335468).sum := by decide
  have hdescent : baseEnd_3335468 < baseStart_3335468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335532 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_3335532 : Nat := 118140960795 + 3335532 * 2 ^ 59
def prefixEnd_3335532 : Nat := 4983230072969 + 3 ^ 40 * 3335532 * 2
def baseEnd_3335532 : Nat := 1141820769635165966273449

theorem tailTrace_3335532 : CollatzResearch.WordTrace tailWord_3335532 prefixEnd_3335532 1141820769635165966273449 := by
  unfold tailWord_3335532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60828423275972351178740425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81104564367963134904987233 60828423275972351178740425)
  ·
    refine ⟨45621317456979263384055319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60828423275972351178740425 45621317456979263384055319)
    ·
      refine ⟨68431976185468895076082979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45621317456979263384055319 68431976185468895076082979)
      ·
        refine ⟨102647964278203342614124469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68431976185468895076082979 102647964278203342614124469)
        ·
          refine ⟨9623246651081563370074169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102647964278203342614124469 9623246651081563370074169)
          ·
            refine ⟨7217434988311172527555627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9623246651081563370074169 7217434988311172527555627)
            ·
              refine ⟨10826152482466758791333441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217434988311172527555627 10826152482466758791333441)
              ·
                refine ⟨8119614361850069093500081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10826152482466758791333441 8119614361850069093500081)
                ·
                  refine ⟨6089710771387551820125061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8119614361850069093500081 6089710771387551820125061)
                  ·
                    refine ⟨1141820769635165966273449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6089710771387551820125061 1141820769635165966273449)
                    ·
                      rfl

theorem cell22_3335532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_3335532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335532 prefixEnd_3335532 := by exact prefixLift 3335532
  have htrace : WordTrace (prefixWord ++ tailWord_3335532) baseStart_3335532 baseEnd_3335532 := by
    simpa [prefixWord, tailWord_3335532, baseEnd_3335532] using wordTrace_append hprefix tailTrace_3335532
  have hstable : (prefixWord ++ tailWord_3335532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335532).length < 2 ^ (prefixWord ++ tailWord_3335532).sum := by decide
  have hdescent : baseEnd_3335532 < baseStart_3335532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335596 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_3335596 : Nat := 118140960795 + 3335596 * 2 ^ 59
def prefixEnd_3335596 : Nat := 4983230072969 + 3 ^ 40 * 3335596 * 2
def baseEnd_3335596 : Nat := 1141842678143091132673253

theorem tailTrace_3335596 : CollatzResearch.WordTrace tailWord_3335596 prefixEnd_3335596 1141842678143091132673253 := by
  unfold tailWord_3335596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60829590411856420643905321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81106120549141894191873761 60829590411856420643905321)
  ·
    refine ⟨45622192808892315482928991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60829590411856420643905321 45622192808892315482928991)
    ·
      refine ⟨68433289213338473224393487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45622192808892315482928991 68433289213338473224393487)
      ·
        refine ⟨102649933820007709836590231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68433289213338473224393487 102649933820007709836590231)
        ·
          refine ⟨153974900730011564754885347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102649933820007709836590231 153974900730011564754885347)
          ·
            refine ⟨230962351095017347132328021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153974900730011564754885347 230962351095017347132328021)
            ·
              refine ⟨2706590051894734536706969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 230962351095017347132328021 2706590051894734536706969)
              ·
                refine ⟨2029942538921050902530227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706590051894734536706969 2029942538921050902530227)
                ·
                  refine ⟨3044913808381576353795341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029942538921050902530227 3044913808381576353795341)
                  ·
                    refine ⟨1141842678143091132673253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3044913808381576353795341 1141842678143091132673253)
                    ·
                      rfl

theorem cell22_3335596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_3335596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335596 prefixEnd_3335596 := by exact prefixLift 3335596
  have htrace : WordTrace (prefixWord ++ tailWord_3335596) baseStart_3335596 baseEnd_3335596 := by
    simpa [prefixWord, tailWord_3335596, baseEnd_3335596] using wordTrace_append hprefix tailTrace_3335596
  have hstable : (prefixWord ++ tailWord_3335596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335596).length < 2 ^ (prefixWord ++ tailWord_3335596).sum := by decide
  have hdescent : baseEnd_3335596 < baseStart_3335596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335720 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3335720 : Nat := 118140960795 + 3335720 * 2 ^ 59
def prefixEnd_3335720 : Nat := 4983230072969 + 3 ^ 40 * 3335720 * 2
def baseEnd_3335720 : Nat := 1141885125877196142572873

theorem tailTrace_3335720 : CollatzResearch.WordTrace tailWord_3335720 prefixEnd_3335720 1141885125877196142572873 := by
  unfold tailWord_3335720
  simp only [CollatzResearch.WordTrace]
  refine ⟨60831851737631805232662307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81109135650175740310216409 60831851737631805232662307)
  ·
    refine ⟨91247777606447707848993461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60831851737631805232662307 91247777606447707848993461)
    ·
      refine ⟨8554479150604472610843137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91247777606447707848993461 8554479150604472610843137)
      ·
        refine ⟨6415859362953354458132353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8554479150604472610843137 6415859362953354458132353)
        ·
          refine ⟨4811894522215015843599265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6415859362953354458132353 4811894522215015843599265)
          ·
            refine ⟨3608920891661261882699449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4811894522215015843599265 3608920891661261882699449)
            ·
              refine ⟨2706690668745946412024587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608920891661261882699449 2706690668745946412024587)
              ·
                refine ⟨4060036003118919618036881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706690668745946412024587 4060036003118919618036881)
                ·
                  refine ⟨3045027002339189713527661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060036003118919618036881 3045027002339189713527661)
                  ·
                    refine ⟨1141885125877196142572873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045027002339189713527661 1141885125877196142572873)
                    ·
                      rfl

theorem cell22_3335720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3335720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335720 prefixEnd_3335720 := by exact prefixLift 3335720
  have htrace : WordTrace (prefixWord ++ tailWord_3335720) baseStart_3335720 baseEnd_3335720 := by
    simpa [prefixWord, tailWord_3335720, baseEnd_3335720] using wordTrace_append hprefix tailTrace_3335720
  have hstable : (prefixWord ++ tailWord_3335720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335720).length < 2 ^ (prefixWord ++ tailWord_3335720).sum := by decide
  have hdescent : baseEnd_3335720 < baseStart_3335720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335804 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_3335804 : Nat := 118140960795 + 3335804 * 2 ^ 59
def prefixEnd_3335804 : Nat := 4983230072969 + 3 ^ 40 * 3335804 * 2
def baseEnd_3335804 : Nat := 1141913880793847923472615

theorem tailTrace_3335804 : CollatzResearch.WordTrace tailWord_3335804 prefixEnd_3335804 1141913880793847923472615 := by
  unfold tailWord_3335804
  simp only [CollatzResearch.WordTrace]
  refine ⟨60833383603479646405691233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81111178137972861874254977 60833383603479646405691233)
  ·
    refine ⟨45625037702609734804268425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60833383603479646405691233 45625037702609734804268425)
    ·
      refine ⟨34218778276957301103201319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45625037702609734804268425 34218778276957301103201319)
      ·
        refine ⟨51328167415435951654801979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34218778276957301103201319 51328167415435951654801979)
        ·
          refine ⟨76992251123153927482202969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51328167415435951654801979 76992251123153927482202969)
          ·
            refine ⟨57744188342365445611652227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76992251123153927482202969 57744188342365445611652227)
            ·
              refine ⟨86616282513548168417478341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57744188342365445611652227 86616282513548168417478341)
              ·
                refine ⟨16240552971290281578277189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86616282513548168417478341 16240552971290281578277189)
                ·
                  refine ⟨3045103682116927795926973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16240552971290281578277189 3045103682116927795926973)
                  ·
                    refine ⟨1141913880793847923472615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045103682116927795926973 1141913880793847923472615)
                    ·
                      rfl

theorem cell22_3335804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_3335804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335804 prefixEnd_3335804 := by exact prefixLift 3335804
  have htrace : WordTrace (prefixWord ++ tailWord_3335804) baseStart_3335804 baseEnd_3335804 := by
    simpa [prefixWord, tailWord_3335804, baseEnd_3335804] using wordTrace_append hprefix tailTrace_3335804
  have hstable : (prefixWord ++ tailWord_3335804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335804).length < 2 ^ (prefixWord ++ tailWord_3335804).sum := by decide
  have hdescent : baseEnd_3335804 < baseStart_3335804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335838 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3335838 : Nat := 118140960795 + 3335838 * 2 ^ 59
def prefixEnd_3335838 : Nat := 4983230072969 + 3 ^ 40 * 3335838 * 2
def baseEnd_3335838 : Nat := 1141925519688683168122511

theorem tailTrace_3335838 : CollatzResearch.WordTrace tailWord_3335838 prefixEnd_3335838 1141925519688683168122511 := by
  unfold tailWord_3335838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208500911104514577265021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81112004859224077745413445 15208500911104514577265021)
  ·
    refine ⟨5703187841664192966474383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15208500911104514577265021 5703187841664192966474383)
    ·
      refine ⟨8554781762496289449711575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703187841664192966474383 8554781762496289449711575)
      ·
        refine ⟨12832172643744434174567363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8554781762496289449711575 12832172643744434174567363)
        ·
          refine ⟨19248258965616651261851045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832172643744434174567363 19248258965616651261851045)
          ·
            refine ⟨3609048556053122111597071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19248258965616651261851045 3609048556053122111597071)
            ·
              refine ⟨5413572834079683167395607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609048556053122111597071 5413572834079683167395607)
              ·
                refine ⟨8120359251119524751093411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5413572834079683167395607 8120359251119524751093411)
                ·
                  refine ⟨12180538876679287126640117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120359251119524751093411 12180538876679287126640117)
                  ·
                    refine ⟨1141925519688683168122511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12180538876679287126640117 1141925519688683168122511)
                    ·
                      rfl

theorem cell22_3335838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3335838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335838 prefixEnd_3335838 := by exact prefixLift 3335838
  have htrace : WordTrace (prefixWord ++ tailWord_3335838) baseStart_3335838 baseEnd_3335838 := by
    simpa [prefixWord, tailWord_3335838, baseEnd_3335838] using wordTrace_append hprefix tailTrace_3335838
  have hstable : (prefixWord ++ tailWord_3335838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335838).length < 2 ^ (prefixWord ++ tailWord_3335838).sum := by decide
  have hdescent : baseEnd_3335838 < baseStart_3335838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335874 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3335874 : Nat := 118140960795 + 3335874 * 2 ^ 59
def prefixEnd_3335874 : Nat := 4983230072969 + 3 ^ 40 * 3335874 * 2
def baseEnd_3335874 : Nat := 380645947741463691407467

theorem tailTrace_3335874 : CollatzResearch.WordTrace tailWord_3335874 prefixEnd_3335874 380645947741463691407467 := by
  unfold tailWord_3335874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30417330079176423691607669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81112880211137129844287117 30417330079176423691607669)
  ·
    refine ⟨2851624694922789721088219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30417330079176423691607669 2851624694922789721088219)
    ·
      refine ⟨4277437042384184581632329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851624694922789721088219 4277437042384184581632329)
      ·
        refine ⟨3208077781788138436224247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277437042384184581632329 3208077781788138436224247)
        ·
          refine ⟨4812116672682207654336371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208077781788138436224247 4812116672682207654336371)
          ·
            refine ⟨7218175009023311481504557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812116672682207654336371 7218175009023311481504557)
            ·
              refine ⟨2706815628383741805564209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7218175009023311481504557 2706815628383741805564209)
              ·
                refine ⟨2030111721287806354173157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706815628383741805564209 2030111721287806354173157)
                ·
                  refine ⟨380645947741463691407467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030111721287806354173157 380645947741463691407467)
                  ·
                    rfl

theorem cell22_3335874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3335874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335874 prefixEnd_3335874 := by exact prefixLift 3335874
  have htrace : WordTrace (prefixWord ++ tailWord_3335874) baseStart_3335874 baseEnd_3335874 := by
    simpa [prefixWord, tailWord_3335874, baseEnd_3335874] using wordTrace_append hprefix tailTrace_3335874
  have hstable : (prefixWord ++ tailWord_3335874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335874).length < 2 ^ (prefixWord ++ tailWord_3335874).sum := by decide
  have hdescent : baseEnd_3335874 < baseStart_3335874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335879 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 5]
def baseStart_3335879 : Nat := 118140960795 + 3335879 * 2 ^ 59
def prefixEnd_3335879 : Nat := 4983230072969 + 3 ^ 40 * 3335879 * 2
def baseEnd_3335879 : Nat := 380646518275524242615795

theorem tailTrace_3335879 : CollatzResearch.WordTrace tailWord_3335879 prefixEnd_3335879 380646518275524242615795 := by
  unfold tailWord_3335879
  simp only [CollatzResearch.WordTrace]
  refine ⟨121669502681687580620362691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81113001787791720413575127 121669502681687580620362691)
  ·
    refine ⟨182504254022531370930544037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121669502681687580620362691 182504254022531370930544037)
    ·
      refine ⟨34219547629224632049477007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182504254022531370930544037 34219547629224632049477007)
      ·
        refine ⟨51329321443836948074215511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34219547629224632049477007 51329321443836948074215511)
        ·
          refine ⟨76993982165755422111323267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51329321443836948074215511 76993982165755422111323267)
          ·
            refine ⟨115490973248633133166984901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76993982165755422111323267 115490973248633133166984901)
            ·
              refine ⟨21654557484118712468809669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115490973248633133166984901 21654557484118712468809669)
              ·
                refine ⟨4060229528272258587901813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21654557484118712468809669 4060229528272258587901813)
                ·
                  refine ⟨380646518275524242615795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4060229528272258587901813 380646518275524242615795)
                  ·
                    rfl

theorem cell22_3335879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 5].length) (baseStart_3335879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335879 prefixEnd_3335879 := by exact prefixLift 3335879
  have htrace : WordTrace (prefixWord ++ tailWord_3335879) baseStart_3335879 baseEnd_3335879 := by
    simpa [prefixWord, tailWord_3335879, baseEnd_3335879] using wordTrace_append hprefix tailTrace_3335879
  have hstable : (prefixWord ++ tailWord_3335879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335879).length < 2 ^ (prefixWord ++ tailWord_3335879).sum := by decide
  have hdescent : baseEnd_3335879 < baseStart_3335879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335934 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_3335934 : Nat := 118140960795 + 3335934 * 2 ^ 59
def prefixEnd_3335934 : Nat := 4983230072969 + 3 ^ 40 * 3335934 * 2
def baseEnd_3335934 : Nat := 1141958382450570917722217

theorem tailTrace_3335934 : CollatzResearch.WordTrace tailWord_3335934 prefixEnd_3335934 1141958382450570917722217 := by
  unfold tailWord_3335934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208938587061040626701857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81114339130992216675743237 15208938587061040626701857)
  ·
    refine ⟨11406703940295780470026393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15208938587061040626701857 11406703940295780470026393)
    ·
      refine ⟨8555027955221835352519795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11406703940295780470026393 8555027955221835352519795)
      ·
        refine ⟨12832541932832753028779693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555027955221835352519795 12832541932832753028779693)
        ·
          refine ⟨4812203224812282385792385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12832541932832753028779693 4812203224812282385792385)
          ·
            refine ⟨3609152418609211789344289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812203224812282385792385 3609152418609211789344289)
            ·
              refine ⟨2706864313956908842008217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609152418609211789344289 2706864313956908842008217)
              ·
                refine ⟨2030148235467681631506163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706864313956908842008217 2030148235467681631506163)
                ·
                  refine ⟨3045222353201522447259245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030148235467681631506163 3045222353201522447259245)
                  ·
                    refine ⟨1141958382450570917722217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045222353201522447259245 1141958382450570917722217)
                    ·
                      rfl

theorem cell22_3335934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_3335934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335934 prefixEnd_3335934 := by exact prefixLift 3335934
  have htrace : WordTrace (prefixWord ++ tailWord_3335934) baseStart_3335934 baseEnd_3335934 := by
    simpa [prefixWord, tailWord_3335934, baseEnd_3335934] using wordTrace_append hprefix tailTrace_3335934
  have hstable : (prefixWord ++ tailWord_3335934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335934).length < 2 ^ (prefixWord ++ tailWord_3335934).sum := by decide
  have hdescent : baseEnd_3335934 < baseStart_3335934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335971 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 2, 4]
def baseStart_3335971 : Nat := 118140960795 + 3335971 * 2 ^ 59
def prefixEnd_3335971 : Nat := 4983230072969 + 3 ^ 40 * 3335971 * 2
def baseEnd_3335971 : Nat := 1141971048306715154547103

theorem tailTrace_3335971 : CollatzResearch.WordTrace tailWord_3335971 prefixEnd_3335971 1141971048306715154547103 := by
  unfold tailWord_3335971
  simp only [CollatzResearch.WordTrace]
  refine ⟨121672858197354280332711767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81115238798236186888474511 121672858197354280332711767)
  ·
    refine ⟨182509287296031420499067651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121672858197354280332711767 182509287296031420499067651)
    ·
      refine ⟨273763930944047130748601477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182509287296031420499067651 273763930944047130748601477)
      ·
        refine ⟨51330737052008837015362777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273763930944047130748601477 51330737052008837015362777)
        ·
          refine ⟨38498052789006627761522083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51330737052008837015362777 38498052789006627761522083)
          ·
            refine ⟨57747079183509941642283125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38498052789006627761522083 57747079183509941642283125)
            ·
              refine ⟨5413788673454057028964043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57747079183509941642283125 5413788673454057028964043)
              ·
                refine ⟨8120683010181085543446065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5413788673454057028964043 8120683010181085543446065)
                ·
                  refine ⟨6090512257635814157584549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8120683010181085543446065 6090512257635814157584549)
                  ·
                    refine ⟨1141971048306715154547103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6090512257635814157584549 1141971048306715154547103)
                    ·
                      rfl

theorem cell22_3335971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].length) (baseStart_3335971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335971 prefixEnd_3335971 := by exact prefixLift 3335971
  have htrace : WordTrace (prefixWord ++ tailWord_3335971) baseStart_3335971 baseEnd_3335971 := by
    simpa [prefixWord, tailWord_3335971, baseEnd_3335971] using wordTrace_append hprefix tailTrace_3335971
  have hstable : (prefixWord ++ tailWord_3335971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335971).length < 2 ^ (prefixWord ++ tailWord_3335971).sum := by decide
  have hdescent : baseEnd_3335971 < baseStart_3335971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335990 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3335990 : Nat := 118140960795 + 3335990 * 2 ^ 59
def prefixEnd_3335990 : Nat := 4983230072969 + 3 ^ 40 * 3335990 * 2
def baseEnd_3335990 : Nat := 1141977552395005438322045

theorem tailTrace_3335990 : CollatzResearch.WordTrace tailWord_3335990 prefixEnd_3335990 1141977552395005438322045 := by
  unfold tailWord_3335990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604596949017840411103339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81115700789523631051768949 7604596949017840411103339)
  ·
    refine ⟨11406895423526760616655009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7604596949017840411103339 11406895423526760616655009)
    ·
      refine ⟨8555171567645070462491257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11406895423526760616655009 8555171567645070462491257)
      ·
        refine ⟨6416378675733802846868443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8555171567645070462491257 6416378675733802846868443)
        ·
          refine ⟨9624568013600704270302665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416378675733802846868443 9624568013600704270302665)
          ·
            refine ⟨7218426010200528202726999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9624568013600704270302665 7218426010200528202726999)
            ·
              refine ⟨10827639015300792304090499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218426010200528202726999 10827639015300792304090499)
              ·
                refine ⟨16241458522951188456135749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10827639015300792304090499 16241458522951188456135749)
                ·
                  refine ⟨3045273473053347835525453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16241458522951188456135749 3045273473053347835525453)
                  ·
                    refine ⟨1141977552395005438322045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045273473053347835525453 1141977552395005438322045)
                    ·
                      rfl

theorem cell22_3335990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3335990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3335990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3335990 prefixEnd_3335990 := by exact prefixLift 3335990
  have htrace : WordTrace (prefixWord ++ tailWord_3335990) baseStart_3335990 baseEnd_3335990 := by
    simpa [prefixWord, tailWord_3335990, baseEnd_3335990] using wordTrace_append hprefix tailTrace_3335990
  have hstable : (prefixWord ++ tailWord_3335990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335990).length < 2 ^ (prefixWord ++ tailWord_3335990).sum := by decide
  have hdescent : baseEnd_3335990 < baseStart_3335990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336018 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_3336018 : Nat := 118140960795 + 3336018 * 2 ^ 59
def prefixEnd_3336018 : Nat := 4983230072969 + 3 ^ 40 * 3336018 * 2
def baseEnd_3336018 : Nat := 1141987137367222698621959

theorem tailTrace_3336018 : CollatzResearch.WordTrace tailWord_3336018 prefixEnd_3336018 1141987137367222698621959 := by
  unfold tailWord_3336018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30418643107046001839918177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81116381618789338239781805 30418643107046001839918177)
  ·
    refine ⟨22813982330284501379938633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30418643107046001839918177 22813982330284501379938633)
    ·
      refine ⟨17110486747713376034953975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22813982330284501379938633 17110486747713376034953975)
      ·
        refine ⟨25665730121570064052430963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17110486747713376034953975 25665730121570064052430963)
        ·
          refine ⟨38498595182355096078646445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25665730121570064052430963 38498595182355096078646445)
          ·
            refine ⟨14436973193383161029492417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38498595182355096078646445 14436973193383161029492417)
            ·
              refine ⟨10827729895037370772119313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14436973193383161029492417 10827729895037370772119313)
              ·
                refine ⟨8120797421278028079089485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10827729895037370772119313 8120797421278028079089485)
                ·
                  refine ⟨3045299032979260529658557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8120797421278028079089485 3045299032979260529658557)
                  ·
                    refine ⟨1141987137367222698621959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045299032979260529658557 1141987137367222698621959)
                    ·
                      rfl

theorem cell22_3336018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_3336018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336018 prefixEnd_3336018 := by exact prefixLift 3336018
  have htrace : WordTrace (prefixWord ++ tailWord_3336018) baseStart_3336018 baseEnd_3336018 := by
    simpa [prefixWord, tailWord_3336018, baseEnd_3336018] using wordTrace_append hprefix tailTrace_3336018
  have hstable : (prefixWord ++ tailWord_3336018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336018).length < 2 ^ (prefixWord ++ tailWord_3336018).sum := by decide
  have hdescent : baseEnd_3336018 < baseStart_3336018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336061 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_3336061 : Nat := 118140960795 + 3336061 * 2 ^ 59
def prefixEnd_3336061 : Nat := 4983230072969 + 3 ^ 40 * 3336061 * 2
def baseEnd_3336061 : Nat := 1142001857145984919796827

theorem tailTrace_3336061 : CollatzResearch.WordTrace tailWord_3336061 prefixEnd_3336061 1142001857145984919796827 := by
  unfold tailWord_3336061
  simp only [CollatzResearch.WordTrace]
  refine ⟨121676140767028225703488037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81117427178018817135658691 121676140767028225703488037)
  ·
    refine ⟨22814276393817792319404007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121676140767028225703488037 22814276393817792319404007)
    ·
      refine ⟨34221414590726688479106011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22814276393817792319404007 34221414590726688479106011)
      ·
        refine ⟨51332121886090032718659017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34221414590726688479106011 51332121886090032718659017)
        ·
          refine ⟨38499091414567524538994263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51332121886090032718659017 38499091414567524538994263)
          ·
            refine ⟨57748637121851286808491395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38499091414567524538994263 57748637121851286808491395)
            ·
              refine ⟨86622955682776930212737093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57748637121851286808491395 86622955682776930212737093)
              ·
                refine ⟨16241804190520674414888205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86622955682776930212737093 16241804190520674414888205)
                ·
                  refine ⟨6090676571445252905583077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16241804190520674414888205 6090676571445252905583077)
                  ·
                    refine ⟨1142001857145984919796827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6090676571445252905583077 1142001857145984919796827)
                    ·
                      rfl

theorem cell22_3336061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_3336061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336061 prefixEnd_3336061 := by exact prefixLift 3336061
  have htrace : WordTrace (prefixWord ++ tailWord_3336061) baseStart_3336061 baseEnd_3336061 := by
    simpa [prefixWord, tailWord_3336061, baseEnd_3336061] using wordTrace_append hprefix tailTrace_3336061
  have hstable : (prefixWord ++ tailWord_3336061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336061).length < 2 ^ (prefixWord ++ tailWord_3336061).sum := by decide
  have hdescent : baseEnd_3336061 < baseStart_3336061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336065 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 5]
def baseStart_3336065 : Nat := 118140960795 + 3336065 * 2 ^ 59
def prefixEnd_3336065 : Nat := 4983230072969 + 3 ^ 40 * 3336065 * 2
def baseEnd_3336065 : Nat := 380667742142576747565605

theorem tailTrace_3336065 : CollatzResearch.WordTrace tailWord_3336065 prefixEnd_3336065 380667742142576747565605 := by
  unfold tailWord_3336065
  simp only [CollatzResearch.WordTrace]
  refine ⟨121676286659013734386633649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81117524439342489591089099 121676286659013734386633649)
  ·
    refine ⟨91257214994260300789975237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121676286659013734386633649 91257214994260300789975237)
    ·
      refine ⟨17110727811423806398120357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91257214994260300789975237 17110727811423806398120357)
      ·
        refine ⟨3208261464641963699647567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17110727811423806398120357 3208261464641963699647567)
        ·
          refine ⟨4812392196962945549471351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208261464641963699647567 4812392196962945549471351)
          ·
            refine ⟨7218588295444418324207027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812392196962945549471351 7218588295444418324207027)
            ·
              refine ⟨10827882443166627486310541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218588295444418324207027 10827882443166627486310541)
              ·
                refine ⟨4060455916187485307366453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10827882443166627486310541 4060455916187485307366453)
                ·
                  refine ⟨380667742142576747565605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4060455916187485307366453 380667742142576747565605)
                  ·
                    rfl

theorem cell22_3336065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_3336065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336065 prefixEnd_3336065 := by exact prefixLift 3336065
  have htrace : WordTrace (prefixWord ++ tailWord_3336065) baseStart_3336065 baseEnd_3336065 := by
    simpa [prefixWord, tailWord_3336065, baseEnd_3336065] using wordTrace_append hprefix tailTrace_3336065
  have hstable : (prefixWord ++ tailWord_3336065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336065).length < 2 ^ (prefixWord ++ tailWord_3336065).sum := by decide
  have hdescent : baseEnd_3336065 < baseStart_3336065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336125 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_3336125 : Nat := 118140960795 + 3336125 * 2 ^ 59
def prefixEnd_3336125 : Nat := 4983230072969 + 3 ^ 40 * 3336125 * 2
def baseEnd_3336125 : Nat := 1142023765653910086196631

theorem tailTrace_3336125 : CollatzResearch.WordTrace tailWord_3336125 prefixEnd_3336125 1142023765653910086196631 := by
  unfold tailWord_3336125
  simp only [CollatzResearch.WordTrace]
  refine ⟨121678475038796364633817829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81118983359197576422545219 121678475038796364633817829)
  ·
    refine ⟨22814714069774318368840843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121678475038796364633817829 22814714069774318368840843)
    ·
      refine ⟨34222071104661477553261265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22814714069774318368840843 34222071104661477553261265)
      ·
        refine ⟨25666553328496108164945949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34222071104661477553261265 25666553328496108164945949)
        ·
          refine ⟨9624957498186040561854731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25666553328496108164945949 9624957498186040561854731)
          ·
            refine ⟨14437436247279060842782097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624957498186040561854731 14437436247279060842782097)
            ·
              refine ⟨10828077185459295632086573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14437436247279060842782097 10828077185459295632086573)
              ·
                refine ⟨4060528944547235862032465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10828077185459295632086573 4060528944547235862032465)
                ·
                  refine ⟨3045396708410426896524349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060528944547235862032465 3045396708410426896524349)
                  ·
                    refine ⟨1142023765653910086196631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045396708410426896524349 1142023765653910086196631)
                    ·
                      rfl

theorem cell22_3336125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_3336125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336125 prefixEnd_3336125 := by exact prefixLift 3336125
  have htrace : WordTrace (prefixWord ++ tailWord_3336125) baseStart_3336125 baseEnd_3336125 := by
    simpa [prefixWord, tailWord_3336125, baseEnd_3336125] using wordTrace_append hprefix tailTrace_3336125
  have hstable : (prefixWord ++ tailWord_3336125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336125).length < 2 ^ (prefixWord ++ tailWord_3336125).sum := by decide
  have hdescent : baseEnd_3336125 < baseStart_3336125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336140 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_3336140 : Nat := 118140960795 + 3336140 * 2 ^ 59
def prefixEnd_3336140 : Nat := 4983230072969 + 3 ^ 40 * 3336140 * 2
def baseEnd_3336140 : Nat := 1142028900460455047071585

theorem tailTrace_3336140 : CollatzResearch.WordTrace tailWord_3336140 prefixEnd_3336140 1142028900460455047071585 := by
  unfold tailWord_3336140
  simp only [CollatzResearch.WordTrace]
  refine ⟨60839511066871011097806937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81119348089161348130409249 60839511066871011097806937)
  ·
    refine ⟨45629633300153258323355203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60839511066871011097806937 45629633300153258323355203)
    ·
      refine ⟨68444449950229887485032805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45629633300153258323355203 68444449950229887485032805)
      ·
        refine ⟨12833334365668103903443651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68444449950229887485032805 12833334365668103903443651)
        ·
          refine ⟨19250001548502155855165477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12833334365668103903443651 19250001548502155855165477)
          ·
            refine ⟨3609375290344154222843527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19250001548502155855165477 3609375290344154222843527)
            ·
              refine ⟨5414062935516231334265291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609375290344154222843527 5414062935516231334265291)
              ·
                refine ⟨8121094403274347001397937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414062935516231334265291 8121094403274347001397937)
                ·
                  refine ⟨6090820802455760251048453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121094403274347001397937 6090820802455760251048453)
                  ·
                    refine ⟨1142028900460455047071585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6090820802455760251048453 1142028900460455047071585)
                    ·
                      rfl

theorem cell22_3336140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_3336140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336140 prefixEnd_3336140 := by exact prefixLift 3336140
  have htrace : WordTrace (prefixWord ++ tailWord_3336140) baseStart_3336140 baseEnd_3336140 := by
    simpa [prefixWord, tailWord_3336140, baseEnd_3336140] using wordTrace_append hprefix tailTrace_3336140
  have hstable : (prefixWord ++ tailWord_3336140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336140).length < 2 ^ (prefixWord ++ tailWord_3336140).sum := by decide
  have hdescent : baseEnd_3336140 < baseStart_3336140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336170 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3336170 : Nat := 118140960795 + 3336170 * 2 ^ 59
def prefixEnd_3336170 : Nat := 4983230072969 + 3 ^ 40 * 3336170 * 2
def baseEnd_3336170 : Nat := 1142039170073544968821493

theorem tailTrace_3336170 : CollatzResearch.WordTrace tailWord_3336170 prefixEnd_3336170 1142039170073544968821493 := by
  unfold tailWord_3336170
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420029080908334329801491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81120077549088891546137309 30420029080908334329801491)
  ·
    refine ⟨45630043621362501494702237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30420029080908334329801491 45630043621362501494702237)
    ·
      refine ⟨17111266358010938060513339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45630043621362501494702237 17111266358010938060513339)
      ·
        refine ⟨25666899537016407090770009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17111266358010938060513339 25666899537016407090770009)
        ·
          refine ⟨19250174652762305318077507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25666899537016407090770009 19250174652762305318077507)
          ·
            refine ⟨28875261979143457977116261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19250174652762305318077507 28875261979143457977116261)
            ·
              refine ⟨5414111621089398370709299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28875261979143457977116261 5414111621089398370709299)
              ·
                refine ⟨8121167431634097556063949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414111621089398370709299 8121167431634097556063949)
                ·
                  refine ⟨3045437786862786583523981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8121167431634097556063949 3045437786862786583523981)
                  ·
                    refine ⟨1142039170073544968821493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045437786862786583523981 1142039170073544968821493)
                    ·
                      rfl

theorem cell22_3336170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3336170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336170 prefixEnd_3336170 := by exact prefixLift 3336170
  have htrace : WordTrace (prefixWord ++ tailWord_3336170) baseStart_3336170 baseEnd_3336170 := by
    simpa [prefixWord, tailWord_3336170, baseEnd_3336170] using wordTrace_append hprefix tailTrace_3336170
  have hstable : (prefixWord ++ tailWord_3336170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336170).length < 2 ^ (prefixWord ++ tailWord_3336170).sum := by decide
  have hdescent : baseEnd_3336170 < baseStart_3336170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336211 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 8]
def baseStart_3336211 : Nat := 118140960795 + 3336211 * 2 ^ 59
def prefixEnd_3336211 : Nat := 4983230072969 + 3 ^ 40 * 3336211 * 2
def baseEnd_3336211 : Nat := 380684401737144842848789

theorem tailTrace_3336211 : CollatzResearch.WordTrace tailWord_3336211 prefixEnd_3336211 380684401737144842848789 := by
  unfold tailWord_3336211
  simp only [CollatzResearch.WordTrace]
  refine ⟨121681611716484801321448487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81121074477656534214298991 121681611716484801321448487)
  ·
    refine ⟨182522417574727201982172731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121681611716484801321448487 182522417574727201982172731)
    ·
      refine ⟨273783626362090802973259097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182522417574727201982172731 273783626362090802973259097)
      ·
        refine ⟨205337719771568102229944323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273783626362090802973259097 205337719771568102229944323)
        ·
          refine ⟨308006579657352153344916485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205337719771568102229944323 308006579657352153344916485)
          ·
            refine ⟨57751233685753528752171841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308006579657352153344916485 57751233685753528752171841)
            ·
              refine ⟨43313425264315146564128881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57751233685753528752171841 43313425264315146564128881)
              ·
                refine ⟨32485068948236359923096661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43313425264315146564128881 32485068948236359923096661)
                ·
                  refine ⟨380684401737144842848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32485068948236359923096661 380684401737144842848789)
                  ·
                    rfl

theorem cell22_3336211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_3336211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336211 prefixEnd_3336211 := by exact prefixLift 3336211
  have htrace : WordTrace (prefixWord ++ tailWord_3336211) baseStart_3336211 baseEnd_3336211 := by
    simpa [prefixWord, tailWord_3336211, baseEnd_3336211] using wordTrace_append hprefix tailTrace_3336211
  have hstable : (prefixWord ++ tailWord_3336211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336211).length < 2 ^ (prefixWord ++ tailWord_3336211).sum := by decide
  have hdescent : baseEnd_3336211 < baseStart_3336211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336277 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3336277 : Nat := 118140960795 + 3336277 * 2 ^ 59
def prefixEnd_3336277 : Nat := 4983230072969 + 3 ^ 40 * 3336277 * 2
def baseEnd_3336277 : Nat := 1142075798360232356396165

theorem tailTrace_3336277 : CollatzResearch.WordTrace tailWord_3336277 prefixEnd_3336277 1142075798360232356396165 := by
  unfold tailWord_3336277
  simp only [CollatzResearch.WordTrace]
  refine ⟨121684018934245694593351085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81122679289497129728900723 121684018934245694593351085)
  ·
    refine ⟨45631507100342135472506657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121684018934245694593351085 45631507100342135472506657)
    ·
      refine ⟨34223630325256601604379993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45631507100342135472506657 34223630325256601604379993)
      ·
        refine ⟨25667722743942451203284995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34223630325256601604379993 25667722743942451203284995)
        ·
          refine ⟨38501584115913676804927493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25667722743942451203284995 38501584115913676804927493)
          ·
            refine ⟨7219047021733814400923905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38501584115913676804927493 7219047021733814400923905)
            ·
              refine ⟨5414285266300360800692929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7219047021733814400923905 5414285266300360800692929)
              ·
                refine ⟨4060713949725270600519697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5414285266300360800692929 4060713949725270600519697)
                ·
                  refine ⟨3045535462293952950389773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060713949725270600519697 3045535462293952950389773)
                  ·
                    refine ⟨1142075798360232356396165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045535462293952950389773 1142075798360232356396165)
                    ·
                      rfl

theorem cell22_3336277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3336277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336277 prefixEnd_3336277 := by exact prefixLift 3336277
  have htrace : WordTrace (prefixWord ++ tailWord_3336277) baseStart_3336277 baseEnd_3336277 := by
    simpa [prefixWord, tailWord_3336277, baseEnd_3336277] using wordTrace_append hprefix tailTrace_3336277
  have hstable : (prefixWord ++ tailWord_3336277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336277).length < 2 ^ (prefixWord ++ tailWord_3336277).sum := by decide
  have hdescent : baseEnd_3336277 < baseStart_3336277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336305 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_3336305 : Nat := 118140960795 + 3336305 * 2 ^ 59
def prefixEnd_3336305 : Nat := 4983230072969 + 3 ^ 40 * 3336305 * 2
def baseEnd_3336305 : Nat := 1142085383332449616696079

theorem tailTrace_3336305 : CollatzResearch.WordTrace tailWord_3336305 prefixEnd_3336305 1142085383332449616696079 := by
  unfold tailWord_3336305
  simp only [CollatzResearch.WordTrace]
  refine ⟨121685040178144255375370369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81123360118762836916913579 121685040178144255375370369)
  ·
    refine ⟨91263780133608191531527777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121685040178144255375370369 91263780133608191531527777)
    ·
      refine ⟨68447835100206143648645833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91263780133608191531527777 68447835100206143648645833)
      ·
        refine ⟨51335876325154607736484375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68447835100206143648645833 51335876325154607736484375)
        ·
          refine ⟨77003814487731911604726563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51335876325154607736484375 77003814487731911604726563)
          ·
            refine ⟨115505721731597867407089845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77003814487731911604726563 115505721731597867407089845)
            ·
              refine ⟨10828661412337300069414673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115505721731597867407089845 10828661412337300069414673)
              ·
                refine ⟨8121496059252975052061005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828661412337300069414673 8121496059252975052061005)
                ·
                  refine ⟨3045561022219865644522877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8121496059252975052061005 3045561022219865644522877)
                  ·
                    refine ⟨1142085383332449616696079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045561022219865644522877 1142085383332449616696079)
                    ·
                      rfl

theorem cell22_3336305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_3336305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336305 prefixEnd_3336305 := by exact prefixLift 3336305
  have htrace : WordTrace (prefixWord ++ tailWord_3336305) baseStart_3336305 baseEnd_3336305 := by
    simpa [prefixWord, tailWord_3336305, baseEnd_3336305] using wordTrace_append hprefix tailTrace_3336305
  have hstable : (prefixWord ++ tailWord_3336305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336305).length < 2 ^ (prefixWord ++ tailWord_3336305).sum := by decide
  have hdescent : baseEnd_3336305 < baseStart_3336305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336352 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 5]
def baseStart_3336352 : Nat := 118140960795 + 3336352 * 2 ^ 59
def prefixEnd_3336352 : Nat := 4983230072969 + 3 ^ 40 * 3336352 * 2
def baseEnd_3336352 : Nat := 380700490797652386923645

theorem tailTrace_3336352 : CollatzResearch.WordTrace tailWord_3336352 prefixEnd_3336352 380700490797652386923645 := by
  unfold tailWord_3336352
  simp only [CollatzResearch.WordTrace]
  refine ⟨60843377204486991201165655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81124502939315988268220873 60843377204486991201165655)
  ·
    refine ⟨91265065806730486801748483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60843377204486991201165655 91265065806730486801748483)
    ·
      refine ⟨136897598710095730202622725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91265065806730486801748483 136897598710095730202622725)
      ·
        refine ⟨25668299758142949412991761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136897598710095730202622725 25668299758142949412991761)
        ·
          refine ⟨19251224818607212059743821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25668299758142949412991761 19251224818607212059743821)
          ·
            refine ⟨7219209306977704522403933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19251224818607212059743821 7219209306977704522403933)
            ·
              refine ⟨2707203490116639195901475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7219209306977704522403933 2707203490116639195901475)
              ·
                refine ⟨4060805235174958793852213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707203490116639195901475 4060805235174958793852213)
                ·
                  refine ⟨380700490797652386923645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4060805235174958793852213 380700490797652386923645)
                  ·
                    rfl

theorem cell22_3336352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_3336352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336352 prefixEnd_3336352 := by exact prefixLift 3336352
  have htrace : WordTrace (prefixWord ++ tailWord_3336352) baseStart_3336352 baseEnd_3336352 := by
    simpa [prefixWord, tailWord_3336352, baseEnd_3336352] using wordTrace_append hprefix tailTrace_3336352
  have hstable : (prefixWord ++ tailWord_3336352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336352).length < 2 ^ (prefixWord ++ tailWord_3336352).sum := by decide
  have hdescent : baseEnd_3336352 < baseStart_3336352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336373 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3336373 : Nat := 118140960795 + 3336373 * 2 ^ 59
def prefixEnd_3336373 : Nat := 4983230072969 + 3 ^ 40 * 3336373 * 2
def baseEnd_3336373 : Nat := 1142108661122120105995871

theorem tailTrace_3336373 : CollatzResearch.WordTrace tailWord_3336373 prefixEnd_3336373 1142108661122120105995871 := by
  unfold tailWord_3336373
  simp only [CollatzResearch.WordTrace]
  refine ⟨121687520341897902988845773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81125013561265268659230515 121687520341897902988845773)
  ·
    refine ⟨45632820128211713620817165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121687520341897902988845773 45632820128211713620817165)
    ·
      refine ⟨17112307548079392607806437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45632820128211713620817165 17112307548079392607806437)
      ·
        refine ⟨3208557665264886113963707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17112307548079392607806437 3208557665264886113963707)
        ·
          refine ⟨4812836497897329170945561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208557665264886113963707 4812836497897329170945561)
          ·
            refine ⟨3609627373422996878209171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812836497897329170945561 3609627373422996878209171)
            ·
              refine ⟨5414441060134495317313757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609627373422996878209171 5414441060134495317313757)
              ·
                refine ⟨2030415397550435743992659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5414441060134495317313757 2030415397550435743992659)
                ·
                  refine ⟨3045623096325653615988989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030415397550435743992659 3045623096325653615988989)
                  ·
                    refine ⟨1142108661122120105995871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045623096325653615988989 1142108661122120105995871)
                    ·
                      rfl

theorem cell22_3336373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3336373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336373 prefixEnd_3336373 := by exact prefixLift 3336373
  have htrace : WordTrace (prefixWord ++ tailWord_3336373) baseStart_3336373 baseEnd_3336373 := by
    simpa [prefixWord, tailWord_3336373, baseEnd_3336373] using wordTrace_append hprefix tailTrace_3336373
  have hstable : (prefixWord ++ tailWord_3336373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336373).length < 2 ^ (prefixWord ++ tailWord_3336373).sum := by decide
  have hdescent : baseEnd_3336373 < baseStart_3336373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336393 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_3336393 : Nat := 118140960795 + 3336393 * 2 ^ 59
def prefixEnd_3336393 : Nat := 4983230072969 + 3 ^ 40 * 3336393 * 2
def baseEnd_3336393 : Nat := 1142115507530846720495809

theorem tailTrace_3336393 : CollatzResearch.WordTrace tailWord_3336393 prefixEnd_3336393 1142115507530846720495809 := by
  unfold tailWord_3336393
  simp only [CollatzResearch.WordTrace]
  refine ⟨121688249801825446404573833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81125499867883630936382555 121688249801825446404573833)
  ·
    refine ⟨91266187351369084803430375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121688249801825446404573833 91266187351369084803430375)
    ·
      refine ⟨136899281027053627205145563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91266187351369084803430375 136899281027053627205145563)
      ·
        refine ⟨205348921540580440807718345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136899281027053627205145563 205348921540580440807718345)
        ·
          refine ⟨154011691155435330605788759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205348921540580440807718345 154011691155435330605788759)
          ·
            refine ⟨231017536733152995908683139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154011691155435330605788759 231017536733152995908683139)
            ·
              refine ⟨346526305099729493863024709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231017536733152995908683139 346526305099729493863024709)
              ·
                refine ⟨64973682206199280099317133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346526305099729493863024709 64973682206199280099317133)
                ·
                  refine ⟨24365130827324730037243925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64973682206199280099317133 24365130827324730037243925)
                  ·
                    refine ⟨1142115507530846720495809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24365130827324730037243925 1142115507530846720495809)
                    ·
                      rfl

theorem cell22_3336393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_3336393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336393 prefixEnd_3336393 := by exact prefixLift 3336393
  have htrace : WordTrace (prefixWord ++ tailWord_3336393) baseStart_3336393 baseEnd_3336393 := by
    simpa [prefixWord, tailWord_3336393, baseEnd_3336393] using wordTrace_append hprefix tailTrace_3336393
  have hstable : (prefixWord ++ tailWord_3336393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336393).length < 2 ^ (prefixWord ++ tailWord_3336393).sum := by decide
  have hdescent : baseEnd_3336393 < baseStart_3336393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336395 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 4, 3]
def baseStart_3336395 : Nat := 118140960795 + 3336395 * 2 ^ 59
def prefixEnd_3336395 : Nat := 4983230072969 + 3 ^ 40 * 3336395 * 2
def baseEnd_3336395 : Nat := 1142116192171719381945803

theorem tailTrace_3336395 : CollatzResearch.WordTrace tailWord_3336395 prefixEnd_3336395 1142116192171719381945803 := by
  unfold tailWord_3336395
  simp only [CollatzResearch.WordTrace]
  refine ⟨121688322747818200746146639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81125548498545467164097759 121688322747818200746146639)
  ·
    refine ⟨182532484121727301119219959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121688322747818200746146639 182532484121727301119219959)
    ·
      refine ⟨273798726182590951678829939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182532484121727301119219959 273798726182590951678829939)
      ·
        refine ⟨410698089273886427518244909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273798726182590951678829939 410698089273886427518244909)
        ·
          refine ⟨154011783477707410319341841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410698089273886427518244909 154011783477707410319341841)
          ·
            refine ⟨115508837608280557739506381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154011783477707410319341841 115508837608280557739506381)
            ·
              refine ⟨43315814103105209152314893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115508837608280557739506381 43315814103105209152314893)
              ·
                refine ⟨16243430288664453432118085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43315814103105209152314893 16243430288664453432118085)
                ·
                  refine ⟨3045643179124585018522141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16243430288664453432118085 3045643179124585018522141)
                  ·
                    refine ⟨1142116192171719381945803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045643179124585018522141 1142116192171719381945803)
                    ·
                      rfl

theorem cell22_3336395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 3].length) (baseStart_3336395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336395 prefixEnd_3336395 := by exact prefixLift 3336395
  have htrace : WordTrace (prefixWord ++ tailWord_3336395) baseStart_3336395 baseEnd_3336395 := by
    simpa [prefixWord, tailWord_3336395, baseEnd_3336395] using wordTrace_append hprefix tailTrace_3336395
  have hstable : (prefixWord ++ tailWord_3336395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336395).length < 2 ^ (prefixWord ++ tailWord_3336395).sum := by decide
  have hdescent : baseEnd_3336395 < baseStart_3336395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336474 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_3336474 : Nat := 118140960795 + 3336474 * 2 ^ 59
def prefixEnd_3336474 : Nat := 4983230072969 + 3 ^ 40 * 3336474 * 2
def baseEnd_3336474 : Nat := 1142143235486189509220561

theorem tailTrace_3336474 : CollatzResearch.WordTrace tailWord_3336474 prefixEnd_3336474 1142143235486189509220561 := by
  unfold tailWord_3336474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422801028632999309568119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81127469409687998158848317 30422801028632999309568119)
  ·
    refine ⟨45634201542949498964352179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30422801028632999309568119 45634201542949498964352179)
    ·
      refine ⟨68451302314424248446528269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45634201542949498964352179 68451302314424248446528269)
      ·
        refine ⟨25669238367909093167448101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68451302314424248446528269 25669238367909093167448101)
        ·
          refine ⟨4812982193982954968896519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25669238367909093167448101 4812982193982954968896519)
          ·
            refine ⟨7219473290974432453344779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812982193982954968896519 7219473290974432453344779)
            ·
              refine ⟨10829209936461648680017169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219473290974432453344779 10829209936461648680017169)
              ·
                refine ⟨8121907452346236510012877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829209936461648680017169 8121907452346236510012877)
                ·
                  refine ⟨3045715294629838691254829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8121907452346236510012877 3045715294629838691254829)
                  ·
                    refine ⟨1142143235486189509220561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045715294629838691254829 1142143235486189509220561)
                    ·
                      rfl

theorem cell22_3336474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_3336474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336474 prefixEnd_3336474 := by exact prefixLift 3336474
  have htrace : WordTrace (prefixWord ++ tailWord_3336474) baseStart_3336474 baseEnd_3336474 := by
    simpa [prefixWord, tailWord_3336474, baseEnd_3336474] using wordTrace_append hprefix tailTrace_3336474
  have hstable : (prefixWord ++ tailWord_3336474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336474).length < 2 ^ (prefixWord ++ tailWord_3336474).sum := by decide
  have hdescent : baseEnd_3336474 < baseStart_3336474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336515 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 6]
def baseStart_3336515 : Nat := 118140960795 + 3336515 * 2 ^ 59
def prefixEnd_3336515 : Nat := 4983230072969 + 3 ^ 40 * 3336515 * 2
def baseEnd_3336515 : Nat := 380719090208026356315145

theorem tailTrace_3336515 : CollatzResearch.WordTrace tailWord_3336515 prefixEnd_3336515 380719090208026356315145 := by
  unfold tailWord_3336515
  simp only [CollatzResearch.WordTrace]
  refine ⟨121692699507383461240514999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81128466338255640827009999 121692699507383461240514999)
  ·
    refine ⟨182539049261075191860772499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121692699507383461240514999 182539049261075191860772499)
    ·
      refine ⟨273808573891612787791158749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182539049261075191860772499 273808573891612787791158749)
      ·
        refine ⟨102678215209354795421684531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273808573891612787791158749 102678215209354795421684531)
        ·
          refine ⟨154017322814032193132526797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102678215209354795421684531 154017322814032193132526797)
          ·
            refine ⟨57756496055262072424697549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154017322814032193132526797 57756496055262072424697549)
            ·
              refine ⟨21658686020723277159261581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57756496055262072424697549 21658686020723277159261581)
              ·
                refine ⟨8122007257771228934723093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21658686020723277159261581 8122007257771228934723093)
                ·
                  refine ⟨380719090208026356315145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8122007257771228934723093 380719090208026356315145)
                  ·
                    rfl

theorem cell22_3336515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_3336515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336515 prefixEnd_3336515 := by exact prefixLift 3336515
  have htrace : WordTrace (prefixWord ++ tailWord_3336515) baseStart_3336515 baseEnd_3336515 := by
    simpa [prefixWord, tailWord_3336515, baseEnd_3336515] using wordTrace_append hprefix tailTrace_3336515
  have hstable : (prefixWord ++ tailWord_3336515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336515).length < 2 ^ (prefixWord ++ tailWord_3336515).sum := by decide
  have hdescent : baseEnd_3336515 < baseStart_3336515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336532 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3336532 : Nat := 118140960795 + 3336532 * 2 ^ 59
def prefixEnd_3336532 : Nat := 4983230072969 + 3 ^ 40 * 3336532 * 2
def baseEnd_3336532 : Nat := 380721030023832230423461

theorem tailTrace_3336532 : CollatzResearch.WordTrace tailWord_3336532 prefixEnd_3336532 380721030023832230423461 := by
  unfold tailWord_3336532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60846659774160936571941925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81128879698881248762589233 60846659774160936571941925)
  ·
    refine ⟨11408748707655175607239111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60846659774160936571941925 11408748707655175607239111)
    ·
      refine ⟨17113123061482763410858667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11408748707655175607239111 17113123061482763410858667)
      ·
        refine ⟨25669684592224145116288001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17113123061482763410858667 25669684592224145116288001)
        ·
          refine ⟨19252263444168108837216001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25669684592224145116288001 19252263444168108837216001)
          ·
            refine ⟨14439197583126081627912001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19252263444168108837216001 14439197583126081627912001)
            ·
              refine ⟨10829398187344561220934001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14439197583126081627912001 10829398187344561220934001)
              ·
                refine ⟨8122048640508420915700501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829398187344561220934001 8122048640508420915700501)
                ·
                  refine ⟨380721030023832230423461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8122048640508420915700501 380721030023832230423461)
                  ·
                    rfl

theorem cell22_3336532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3336532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336532 prefixEnd_3336532 := by exact prefixLift 3336532
  have htrace : WordTrace (prefixWord ++ tailWord_3336532) baseStart_3336532 baseEnd_3336532 := by
    simpa [prefixWord, tailWord_3336532, baseEnd_3336532] using wordTrace_append hprefix tailTrace_3336532
  have hstable : (prefixWord ++ tailWord_3336532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336532).length < 2 ^ (prefixWord ++ tailWord_3336532).sum := by decide
  have hdescent : baseEnd_3336532 < baseStart_3336532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336547 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 6, 3]
def baseStart_3336547 : Nat := 118140960795 + 3336547 * 2 ^ 59
def prefixEnd_3336547 : Nat := 4983230072969 + 3 ^ 40 * 3336547 * 2
def baseEnd_3336547 : Nat := 1142168224878041652145337

theorem tailTrace_3336547 : CollatzResearch.WordTrace tailWord_3336547 prefixEnd_3336547 1142168224878041652145337 := by
  unfold tailWord_3336547
  simp only [CollatzResearch.WordTrace]
  refine ⟨121693866643267530705679895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81129244428845020470453263 121693866643267530705679895)
  ·
    refine ⟨182540799964901296058519843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121693866643267530705679895 182540799964901296058519843)
    ·
      refine ⟨273811199947351944087779765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182540799964901296058519843 273811199947351944087779765)
      ·
        refine ⟨25669799995064244758229353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273811199947351944087779765 25669799995064244758229353)
        ·
          refine ⟨19252349996298183568672015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25669799995064244758229353 19252349996298183568672015)
          ·
            refine ⟨28878524994447275353008023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19252349996298183568672015 28878524994447275353008023)
            ·
              refine ⟨43317787491670913029512035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28878524994447275353008023 43317787491670913029512035)
              ·
                refine ⟨64976681237506369544268053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43317787491670913029512035 64976681237506369544268053)
                ·
                  refine ⟨3045781933008111072387565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64976681237506369544268053 3045781933008111072387565)
                  ·
                    refine ⟨1142168224878041652145337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045781933008111072387565 1142168224878041652145337)
                    ·
                      rfl

theorem cell22_3336547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 3].length) (baseStart_3336547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336547 prefixEnd_3336547 := by exact prefixLift 3336547
  have htrace : WordTrace (prefixWord ++ tailWord_3336547) baseStart_3336547 baseEnd_3336547 := by
    simpa [prefixWord, tailWord_3336547, baseEnd_3336547] using wordTrace_append hprefix tailTrace_3336547
  have hstable : (prefixWord ++ tailWord_3336547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336547).length < 2 ^ (prefixWord ++ tailWord_3336547).sum := by decide
  have hdescent : baseEnd_3336547 < baseStart_3336547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336549 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 4]
def baseStart_3336549 : Nat := 118140960795 + 3336549 * 2 ^ 59
def prefixEnd_3336549 : Nat := 4983230072969 + 3 ^ 40 * 3336549 * 2
def baseEnd_3336549 : Nat := 380722969839638104531777

theorem tailTrace_3336549 : CollatzResearch.WordTrace tailWord_3336549 prefixEnd_3336549 380722969839638104531777 := by
  unfold tailWord_3336549
  simp only [CollatzResearch.WordTrace]
  refine ⟨121693939589260285047252701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81129293059506856698168467 121693939589260285047252701)
  ·
    refine ⟨45635227345972606892719763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121693939589260285047252701 45635227345972606892719763)
    ·
      refine ⟨68452841018958910339079645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45635227345972606892719763 68452841018958910339079645)
      ·
        refine ⟨25669815382109591377154867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68452841018958910339079645 25669815382109591377154867)
        ·
          refine ⟨38504723073164387065732301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25669815382109591377154867 38504723073164387065732301)
          ·
            refine ⟨14439271152436645149649613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38504723073164387065732301 14439271152436645149649613)
            ·
              refine ⟨5414726682163741931118605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14439271152436645149649613 5414726682163741931118605)
              ·
                refine ⟨2030522505811403224169477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5414726682163741931118605 2030522505811403224169477)
                ·
                  refine ⟨380722969839638104531777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030522505811403224169477 380722969839638104531777)
                  ·
                    rfl

theorem cell22_3336549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_3336549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336549 prefixEnd_3336549 := by exact prefixLift 3336549
  have htrace : WordTrace (prefixWord ++ tailWord_3336549) baseStart_3336549 baseEnd_3336549 := by
    simpa [prefixWord, tailWord_3336549, baseEnd_3336549] using wordTrace_append hprefix tailTrace_3336549
  have hstable : (prefixWord ++ tailWord_3336549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336549).length < 2 ^ (prefixWord ++ tailWord_3336549).sum := by decide
  have hdescent : baseEnd_3336549 < baseStart_3336549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336560 : List Nat := [2, 1, 1, 1, 4, 3, 10]
def baseStart_3336560 : Nat := 118140960795 + 3336560 * 2 ^ 59
def prefixEnd_3336560 : Nat := 4983230072969 + 3 ^ 40 * 3336560 * 2
def baseEnd_3336560 : Nat := 42302691668285701910011

theorem tailTrace_3336560 : CollatzResearch.WordTrace tailWord_3336560 prefixEnd_3336560 42302691668285701910011 := by
  unfold tailWord_3336560
  simp only [CollatzResearch.WordTrace]
  refine ⟨60847170396110216962951567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81129560528146955950602089 60847170396110216962951567)
  ·
    refine ⟨91270755594165325444427351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60847170396110216962951567 91270755594165325444427351)
    ·
      refine ⟨136906133391247988166641027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91270755594165325444427351 136906133391247988166641027)
      ·
        refine ⟨205359200086871982249961541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136906133391247988166641027 205359200086871982249961541)
        ·
          refine ⟨38504850016288496671867789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205359200086871982249961541 38504850016288496671867789)
          ·
            refine ⟨14439318756108186251950421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38504850016288496671867789 14439318756108186251950421)
            ·
              refine ⟨42302691668285701910011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14439318756108186251950421 42302691668285701910011)
              ·
                rfl

theorem cell22_3336560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 10].length) (baseStart_3336560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336560 prefixEnd_3336560 := by exact prefixLift 3336560
  have htrace : WordTrace (prefixWord ++ tailWord_3336560) baseStart_3336560 baseEnd_3336560 := by
    simpa [prefixWord, tailWord_3336560, baseEnd_3336560] using wordTrace_append hprefix tailTrace_3336560
  have hstable : (prefixWord ++ tailWord_3336560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336560).length < 2 ^ (prefixWord ++ tailWord_3336560).sum := by decide
  have hdescent : baseEnd_3336560 < baseStart_3336560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336562 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3336562 : Nat := 118140960795 + 3336562 * 2 ^ 59
def prefixEnd_3336562 : Nat := 4983230072969 + 3 ^ 40 * 3336562 * 2
def baseEnd_3336562 : Nat := 1142173359684586613020291

theorem tailTrace_3336562 : CollatzResearch.WordTrace tailWord_3336562 prefixEnd_3336562 1142173359684586613020291 := by
  unfold tailWord_3336562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30423603434553297066868985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81129609158808792178317293 30423603434553297066868985)
  ·
    refine ⟨22817702575914972800151739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30423603434553297066868985 22817702575914972800151739)
    ·
      refine ⟨34226553863872459200227609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22817702575914972800151739 34226553863872459200227609)
      ·
        refine ⟨25669915397904344400170707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34226553863872459200227609 25669915397904344400170707)
        ·
          refine ⟨38504873096856516600256061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25669915397904344400170707 38504873096856516600256061)
          ·
            refine ⟨14439327411321193725096023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38504873096856516600256061 14439327411321193725096023)
            ·
              refine ⟨21658991116981790587644035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14439327411321193725096023 21658991116981790587644035)
              ·
                refine ⟨32488486675472685881466053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21658991116981790587644035 32488486675472685881466053)
                ·
                  refine ⟨6091591251651128602774885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32488486675472685881466053 6091591251651128602774885)
                  ·
                    refine ⟨1142173359684586613020291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091591251651128602774885 1142173359684586613020291)
                    ·
                      rfl

theorem cell22_3336562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3336562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336562 prefixEnd_3336562 := by exact prefixLift 3336562
  have htrace : WordTrace (prefixWord ++ tailWord_3336562) baseStart_3336562 baseEnd_3336562 := by
    simpa [prefixWord, tailWord_3336562, baseEnd_3336562] using wordTrace_append hprefix tailTrace_3336562
  have hstable : (prefixWord ++ tailWord_3336562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336562).length < 2 ^ (prefixWord ++ tailWord_3336562).sum := by decide
  have hdescent : baseEnd_3336562 < baseStart_3336562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336577 : List Nat := [1, 2, 4, 3, 1, 1, 1, 9]
def baseStart_3336577 : Nat := 118140960795 + 3336577 * 2 ^ 59
def prefixEnd_3336577 : Nat := 4983230072969 + 3 ^ 40 * 3336577 * 2
def baseEnd_3336577 : Nat := 126908721610125730432805

theorem tailTrace_3336577 : CollatzResearch.WordTrace tailWord_3336577 prefixEnd_3336577 126908721610125730432805 := by
  unfold tailWord_3336577
  simp only [CollatzResearch.WordTrace]
  refine ⟨121694960833158845829271985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81129973888772563886181323 121694960833158845829271985)
  ·
    refine ⟨91271220624869134371953989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121694960833158845829271985 91271220624869134371953989)
    ·
      refine ⟨17113353867162962694741373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91271220624869134371953989 17113353867162962694741373)
      ·
        refine ⟨6417507700186111010528015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17113353867162962694741373 6417507700186111010528015)
        ·
          refine ⟨9626261550279166515792023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6417507700186111010528015 9626261550279166515792023)
          ·
            refine ⟨14439392325418749773688035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9626261550279166515792023 14439392325418749773688035)
            ·
              refine ⟨21659088488128124660532053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14439392325418749773688035 21659088488128124660532053)
              ·
                refine ⟨126908721610125730432805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21659088488128124660532053 126908721610125730432805)
                ·
                  rfl

theorem cell22_3336577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 9].length) (baseStart_3336577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336577 prefixEnd_3336577 := by exact prefixLift 3336577
  have htrace : WordTrace (prefixWord ++ tailWord_3336577) baseStart_3336577 baseEnd_3336577 := by
    simpa [prefixWord, tailWord_3336577, baseEnd_3336577] using wordTrace_append hprefix tailTrace_3336577
  have hstable : (prefixWord ++ tailWord_3336577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336577).length < 2 ^ (prefixWord ++ tailWord_3336577).sum := by decide
  have hdescent : baseEnd_3336577 < baseStart_3336577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336596 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3336596 : Nat := 118140960795 + 3336596 * 2 ^ 59
def prefixEnd_3336596 : Nat := 4983230072969 + 3 ^ 40 * 3336596 * 2
def baseEnd_3336596 : Nat := 1142184998579421857670187

theorem tailTrace_3336596 : CollatzResearch.WordTrace tailWord_3336596 prefixEnd_3336596 1142184998579421857670187 := by
  unfold tailWord_3336596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60847826910045006037106821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81130435880060008049475761 60847826910045006037106821)
  ·
    refine ⟨11408967545633438631957529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60847826910045006037106821 11408967545633438631957529)
    ·
      refine ⟨8556725659225078973968147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11408967545633438631957529 8556725659225078973968147)
      ·
        refine ⟨12835088488837618460952221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556725659225078973968147 12835088488837618460952221)
        ·
          refine ⟨4813158183314106922857083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12835088488837618460952221 4813158183314106922857083)
          ·
            refine ⟨7219737274971160384285625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813158183314106922857083 7219737274971160384285625)
            ·
              refine ⟨5414802956228370288214219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7219737274971160384285625 5414802956228370288214219)
              ·
                refine ⟨8122204434342555432321329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414802956228370288214219 8122204434342555432321329)
                ·
                  refine ⟨6091653325756916574240997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8122204434342555432321329 6091653325756916574240997)
                  ·
                    refine ⟨1142184998579421857670187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091653325756916574240997 1142184998579421857670187)
                    ·
                      rfl

theorem cell22_3336596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3336596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336596 prefixEnd_3336596 := by exact prefixLift 3336596
  have htrace : WordTrace (prefixWord ++ tailWord_3336596) baseStart_3336596 baseEnd_3336596 := by
    simpa [prefixWord, tailWord_3336596, baseEnd_3336596] using wordTrace_append hprefix tailTrace_3336596
  have hstable : (prefixWord ++ tailWord_3336596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336596).length < 2 ^ (prefixWord ++ tailWord_3336596).sum := by decide
  have hdescent : baseEnd_3336596 < baseStart_3336596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336626 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_3336626 : Nat := 118140960795 + 3336626 * 2 ^ 59
def prefixEnd_3336626 : Nat := 4983230072969 + 3 ^ 40 * 3336626 * 2
def baseEnd_3336626 : Nat := 1142195268192511779420095

theorem tailTrace_3336626 : CollatzResearch.WordTrace tailWord_3336626 prefixEnd_3336626 1142195268192511779420095 := by
  unfold tailWord_3336626
  simp only [CollatzResearch.WordTrace]
  refine ⟨30424187002495331799451433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81131165339987551465203821 30424187002495331799451433)
  ·
    refine ⟨22818140251871498849588575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30424187002495331799451433 22818140251871498849588575)
    ·
      refine ⟨34227210377807248274382863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22818140251871498849588575 34227210377807248274382863)
      ·
        refine ⟨51340815566710872411574295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34227210377807248274382863 51340815566710872411574295)
        ·
          refine ⟨77011223350066308617361443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51340815566710872411574295 77011223350066308617361443)
          ·
            refine ⟨115516835025099462926042165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77011223350066308617361443 115516835025099462926042165)
            ·
              refine ⟨10829703283603074649316453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115516835025099462926042165 10829703283603074649316453)
              ·
                refine ⟨2030569365675576496746835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10829703283603074649316453 2030569365675576496746835)
                ·
                  refine ⟨3045854048513364745120253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030569365675576496746835 3045854048513364745120253)
                  ·
                    refine ⟨1142195268192511779420095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045854048513364745120253 1142195268192511779420095)
                    ·
                      rfl

theorem cell22_3336626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_3336626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336626 prefixEnd_3336626 := by exact prefixLift 3336626
  have htrace : WordTrace (prefixWord ++ tailWord_3336626) baseStart_3336626 baseEnd_3336626 := by
    simpa [prefixWord, tailWord_3336626, baseEnd_3336626] using wordTrace_append hprefix tailTrace_3336626
  have hstable : (prefixWord ++ tailWord_3336626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336626).length < 2 ^ (prefixWord ++ tailWord_3336626).sum := by decide
  have hdescent : baseEnd_3336626 < baseStart_3336626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336628 : List Nat := [2, 5, 2, 2, 1, 2, 1, 7]
def baseStart_3336628 : Nat := 118140960795 + 3336628 * 2 ^ 59
def prefixEnd_3336628 : Nat := 4983230072969 + 3 ^ 40 * 3336628 * 2
def baseEnd_3336628 : Nat := 126910661425931604541121

theorem tailTrace_3336628 : CollatzResearch.WordTrace tailWord_3336628 prefixEnd_3336628 126910661425931604541121 := by
  unfold tailWord_3336628
  simp only [CollatzResearch.WordTrace]
  refine ⟨60848410477987040769689269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81131213970649387692919025 60848410477987040769689269)
  ·
    refine ⟨5704538482311285072158369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60848410477987040769689269 5704538482311285072158369)
    ·
      refine ⟨4278403861733463804118777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5704538482311285072158369 4278403861733463804118777)
      ·
        refine ⟨3208802896300097853089083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4278403861733463804118777 3208802896300097853089083)
        ·
          refine ⟨4813204344450146779633625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208802896300097853089083 4813204344450146779633625)
          ·
            refine ⟨3609903258337610084725219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813204344450146779633625 3609903258337610084725219)
            ·
              refine ⟨5414854887506415127087829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609903258337610084725219 5414854887506415127087829)
              ·
                refine ⟨126910661425931604541121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5414854887506415127087829 126910661425931604541121)
                ·
                  rfl

theorem cell22_3336628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 7].length) (baseStart_3336628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336628 prefixEnd_3336628 := by exact prefixLift 3336628
  have htrace : WordTrace (prefixWord ++ tailWord_3336628) baseStart_3336628 baseEnd_3336628 := by
    simpa [prefixWord, tailWord_3336628, baseEnd_3336628] using wordTrace_append hprefix tailTrace_3336628
  have hstable : (prefixWord ++ tailWord_3336628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336628).length < 2 ^ (prefixWord ++ tailWord_3336628).sum := by decide
  have hdescent : baseEnd_3336628 < baseStart_3336628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336637 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_3336637 : Nat := 118140960795 + 3336637 * 2 ^ 59
def prefixEnd_3336637 : Nat := 4983230072969 + 3 ^ 40 * 3336637 * 2
def baseEnd_3336637 : Nat := 1142199033717311417395061

theorem tailTrace_3336637 : CollatzResearch.WordTrace tailWord_3336637 prefixEnd_3336637 1142199033717311417395061 := by
  unfold tailWord_3336637
  simp only [CollatzResearch.WordTrace]
  refine ⟨121697149212941476076456165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81131432808627650717637443 121697149212941476076456165)
  ·
    refine ⟨22818215477426526764335531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121697149212941476076456165 22818215477426526764335531)
    ·
      refine ⟨34227323216139790146503297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22818215477426526764335531 34227323216139790146503297)
      ·
        refine ⟨25670492412104842609877473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34227323216139790146503297 25670492412104842609877473)
        ·
          refine ⟨19252869309078631957408105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25670492412104842609877473 19252869309078631957408105)
          ·
            refine ⟨14439651981808973968056079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19252869309078631957408105 14439651981808973968056079)
            ·
              refine ⟨21659477972713460952084119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14439651981808973968056079 21659477972713460952084119)
              ·
                refine ⟨32489216959070191428126179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21659477972713460952084119 32489216959070191428126179)
                ·
                  refine ⟨48733825438605287142189269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32489216959070191428126179 48733825438605287142189269)
                  ·
                    refine ⟨1142199033717311417395061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48733825438605287142189269 1142199033717311417395061)
                    ·
                      rfl

theorem cell22_3336637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_3336637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336637 prefixEnd_3336637 := by exact prefixLift 3336637
  have htrace : WordTrace (prefixWord ++ tailWord_3336637) baseStart_3336637 baseEnd_3336637 := by
    simpa [prefixWord, tailWord_3336637, baseEnd_3336637] using wordTrace_append hprefix tailTrace_3336637
  have hstable : (prefixWord ++ tailWord_3336637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336637).length < 2 ^ (prefixWord ++ tailWord_3336637).sum := by decide
  have hdescent : baseEnd_3336637 < baseStart_3336637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336684 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 4]
def baseStart_3336684 : Nat := 118140960795 + 3336684 * 2 ^ 59
def prefixEnd_3336684 : Nat := 4983230072969 + 3 ^ 40 * 3336684 * 2
def baseEnd_3336684 : Nat := 380738374259272987156639

theorem tailTrace_3336684 : CollatzResearch.WordTrace tailWord_3336684 prefixEnd_3336684 380738374259272987156639 := by
  unfold tailWord_3336684
  simp only [CollatzResearch.WordTrace]
  refine ⟨60849431721885601551708553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81132575629180802068944737 60849431721885601551708553)
  ·
    refine ⟨45637073791414201163781415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60849431721885601551708553 45637073791414201163781415)
    ·
      refine ⟨68455610687121301745672123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45637073791414201163781415 68455610687121301745672123)
      ·
        refine ⟨102683416030681952618508185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68455610687121301745672123 102683416030681952618508185)
        ·
          refine ⟨77012562023011464463881139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102683416030681952618508185 77012562023011464463881139)
          ·
            refine ⟨115518843034517196695821709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77012562023011464463881139 115518843034517196695821709)
            ·
              refine ⟨43319566137943948760933141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115518843034517196695821709 43319566137943948760933141)
              ·
                refine ⟨2030604662716122598168741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43319566137943948760933141 2030604662716122598168741)
                ·
                  refine ⟨380738374259272987156639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030604662716122598168741 380738374259272987156639)
                  ·
                    rfl

theorem cell22_3336684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_3336684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336684 prefixEnd_3336684 := by exact prefixLift 3336684
  have htrace : WordTrace (prefixWord ++ tailWord_3336684) baseStart_3336684 baseEnd_3336684 := by
    simpa [prefixWord, tailWord_3336684, baseEnd_3336684] using wordTrace_append hprefix tailTrace_3336684
  have hstable : (prefixWord ++ tailWord_3336684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336684).length < 2 ^ (prefixWord ++ tailWord_3336684).sum := by decide
  have hdescent : baseEnd_3336684 < baseStart_3336684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336697 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_3336697 : Nat := 118140960795 + 3336697 * 2 ^ 59
def prefixEnd_3336697 : Nat := 4983230072969 + 3 ^ 40 * 3336697 * 2
def baseEnd_3336697 : Nat := 1142219572943491260894877

theorem tailTrace_3336697 : CollatzResearch.WordTrace tailWord_3336697 prefixEnd_3336697 1142219572943491260894877 := by
  unfold tailWord_3336697
  simp only [CollatzResearch.WordTrace]
  refine ⟨121699337592724106323640345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81132891728482737549093563 121699337592724106323640345)
  ·
    refine ⟨91274503194543079742730259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121699337592724106323640345 91274503194543079742730259)
    ·
      refine ⟨136911754791814619614095389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91274503194543079742730259 136911754791814619614095389)
      ·
        refine ⟨51341908046930482355285771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136911754791814619614095389 51341908046930482355285771)
        ·
          refine ⟨77012862070395723532928657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51341908046930482355285771 77012862070395723532928657)
          ·
            refine ⟨57759646552796792649696493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77012862070395723532928657 57759646552796792649696493)
            ·
              refine ⟨21659867457298797243636185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57759646552796792649696493 21659867457298797243636185)
              ·
                refine ⟨16244900592974097932727139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21659867457298797243636185 16244900592974097932727139)
                ·
                  refine ⟨24367350889461146899090709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16244900592974097932727139 24367350889461146899090709)
                  ·
                    refine ⟨1142219572943491260894877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24367350889461146899090709 1142219572943491260894877)
                    ·
                      rfl

theorem cell22_3336697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_3336697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336697 prefixEnd_3336697 := by exact prefixLift 3336697
  have htrace : WordTrace (prefixWord ++ tailWord_3336697) baseStart_3336697 baseEnd_3336697 := by
    simpa [prefixWord, tailWord_3336697, baseEnd_3336697] using wordTrace_append hprefix tailTrace_3336697
  have hstable : (prefixWord ++ tailWord_3336697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336697).length < 2 ^ (prefixWord ++ tailWord_3336697).sum := by decide
  have hdescent : baseEnd_3336697 < baseStart_3336697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336714 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_3336714 : Nat := 118140960795 + 3336714 * 2 ^ 59
def prefixEnd_3336714 : Nat := 4983230072969 + 3 ^ 40 * 3336714 * 2
def baseEnd_3336714 : Nat := 1142225392390908883219825

theorem tailTrace_3336714 : CollatzResearch.WordTrace tailWord_3336714 prefixEnd_3336714 1142225392390908883219825 := by
  unfold tailWord_3336714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30424989408415629556752299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81133305089108345484672797 30424989408415629556752299)
  ·
    refine ⟨45637484112623444335128449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30424989408415629556752299 45637484112623444335128449)
    ·
      refine ⟨34228113084467583251346337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45637484112623444335128449 34228113084467583251346337)
      ·
        refine ⟨25671084813350687438509753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34228113084467583251346337 25671084813350687438509753)
        ·
          refine ⟨19253313610013015578882315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25671084813350687438509753 19253313610013015578882315)
          ·
            refine ⟨28879970415019523368323473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19253313610013015578882315 28879970415019523368323473)
            ·
              refine ⟨21659977811264642526242605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28879970415019523368323473 21659977811264642526242605)
              ·
                refine ⟨8122491679224240947340977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21659977811264642526242605 8122491679224240947340977)
                ·
                  refine ⟨6091868759418180710505733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8122491679224240947340977 6091868759418180710505733)
                  ·
                    refine ⟨1142225392390908883219825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091868759418180710505733 1142225392390908883219825)
                    ·
                      rfl

theorem cell22_3336714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_3336714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336714 prefixEnd_3336714 := by exact prefixLift 3336714
  have htrace : WordTrace (prefixWord ++ tailWord_3336714) baseStart_3336714 baseEnd_3336714 := by
    simpa [prefixWord, tailWord_3336714, baseEnd_3336714] using wordTrace_append hprefix tailTrace_3336714
  have hstable : (prefixWord ++ tailWord_3336714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336714).length < 2 ^ (prefixWord ++ tailWord_3336714).sum := by decide
  have hdescent : baseEnd_3336714 < baseStart_3336714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336718 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3336718 : Nat := 118140960795 + 3336718 * 2 ^ 59
def prefixEnd_3336718 : Nat := 4983230072969 + 3 ^ 40 * 3336718 * 2
def baseEnd_3336718 : Nat := 380742253890884735373271

theorem tailTrace_3336718 : CollatzResearch.WordTrace tailWord_3336718 prefixEnd_3336718 380742253890884735373271 := by
  unfold tailWord_3336718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212512940706003363769351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81133402350432017940103205 15212512940706003363769351)
  ·
    refine ⟨22818769411059005045654027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15212512940706003363769351 22818769411059005045654027)
    ·
      refine ⟨34228154116588507568481041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22818769411059005045654027 34228154116588507568481041)
      ·
        refine ⟨25671115587441380676360781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34228154116588507568481041 25671115587441380676360781)
        ·
          refine ⟨9626668345290517753635293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25671115587441380676360781 9626668345290517753635293)
          ·
            refine ⟨3610000629483944157613235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9626668345290517753635293 3610000629483944157613235)
            ·
              refine ⟨5415000944225916236419853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610000629483944157613235 5415000944225916236419853)
              ·
                refine ⟨2030625354084718588657445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5415000944225916236419853 2030625354084718588657445)
                ·
                  refine ⟨380742253890884735373271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030625354084718588657445 380742253890884735373271)
                  ·
                    rfl

theorem cell22_3336718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3336718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336718 prefixEnd_3336718 := by exact prefixLift 3336718
  have htrace : WordTrace (prefixWord ++ tailWord_3336718) baseStart_3336718 baseEnd_3336718 := by
    simpa [prefixWord, tailWord_3336718, baseEnd_3336718] using wordTrace_append hprefix tailTrace_3336718
  have hstable : (prefixWord ++ tailWord_3336718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336718).length < 2 ^ (prefixWord ++ tailWord_3336718).sum := by decide
  have hdescent : baseEnd_3336718 < baseStart_3336718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336804 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_3336804 : Nat := 118140960795 + 3336804 * 2 ^ 59
def prefixEnd_3336804 : Nat := 4983230072969 + 3 ^ 40 * 3336804 * 2
def baseEnd_3336804 : Nat := 1142256201230178648469549

theorem tailTrace_3336804 : CollatzResearch.WordTrace tailWord_3336804 prefixEnd_3336804 1142256201230178648469549 := by
  unfold tailWord_3336804
  simp only [CollatzResearch.WordTrace]
  refine ⟨60851620101668231798892733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81135493468890975731856977 60851620101668231798892733)
  ·
    refine ⟨22819357538125586924584775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60851620101668231798892733 22819357538125586924584775)
    ·
      refine ⟨34229036307188380386877163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22819357538125586924584775 34229036307188380386877163)
      ·
        refine ⟨51343554460782570580315745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34229036307188380386877163 51343554460782570580315745)
        ·
          refine ⟨38507665845586927935236809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51343554460782570580315745 38507665845586927935236809)
          ·
            refine ⟨28880749384190195951427607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38507665845586927935236809 28880749384190195951427607)
            ·
              refine ⟨43321124076285293927141411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28880749384190195951427607 43321124076285293927141411)
              ·
                refine ⟨64981686114427940890712117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43321124076285293927141411 64981686114427940890712117)
                ·
                  refine ⟨6092033073227619458504261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64981686114427940890712117 6092033073227619458504261)
                  ·
                    refine ⟨1142256201230178648469549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6092033073227619458504261 1142256201230178648469549)
                    ·
                      rfl

theorem cell22_3336804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_3336804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3336804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3336804 prefixEnd_3336804 := by exact prefixLift 3336804
  have htrace : WordTrace (prefixWord ++ tailWord_3336804) baseStart_3336804 baseEnd_3336804 := by
    simpa [prefixWord, tailWord_3336804, baseEnd_3336804] using wordTrace_append hprefix tailTrace_3336804
  have hstable : (prefixWord ++ tailWord_3336804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336804).length < 2 ^ (prefixWord ++ tailWord_3336804).sum := by decide
  have hdescent : baseEnd_3336804 < baseStart_3336804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337037 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3337037 : Nat := 118140960795 + 3337037 * 2 ^ 59
def prefixEnd_3337037 : Nat := 4983230072969 + 3 ^ 40 * 3337037 * 2
def baseEnd_3337037 : Nat := 1142335961891843707393835

theorem tailTrace_3337037 : CollatzResearch.WordTrace tailWord_3337037 prefixEnd_3337037 1142335961891843707393835 := by
  unfold tailWord_3337037
  simp only [CollatzResearch.WordTrace]
  refine ⟨121711738411492344391017365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81141158940994896260678243 121711738411492344391017365)
  ·
    refine ⟨5705237738038703643328939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121711738411492344391017365 5705237738038703643328939)
    ·
      refine ⟨8557856607058055464993409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705237738038703643328939 8557856607058055464993409)
      ·
        refine ⟨6418392455293541598745057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8557856607058055464993409 6418392455293541598745057)
        ·
          refine ⟨4813794341470156199058793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418392455293541598745057 4813794341470156199058793)
          ·
            refine ⟨3610345756102617149294095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813794341470156199058793 3610345756102617149294095)
            ·
              refine ⟨5415518634153925723941143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610345756102617149294095 5415518634153925723941143)
              ·
                refine ⟨8123277951230888585911715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415518634153925723941143 8123277951230888585911715)
                ·
                  refine ⟨12184916926846332878867573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123277951230888585911715 12184916926846332878867573)
                  ·
                    refine ⟨1142335961891843707393835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12184916926846332878867573 1142335961891843707393835)
                    ·
                      rfl

theorem cell22_3337037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3337037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337037 prefixEnd_3337037 := by exact prefixLift 3337037
  have htrace : WordTrace (prefixWord ++ tailWord_3337037) baseStart_3337037 baseEnd_3337037 := by
    simpa [prefixWord, tailWord_3337037, baseEnd_3337037] using wordTrace_append hprefix tailTrace_3337037
  have hstable : (prefixWord ++ tailWord_3337037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337037).length < 2 ^ (prefixWord ++ tailWord_3337037).sum := by decide
  have hdescent : baseEnd_3337037 < baseStart_3337037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337061 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 7]
def baseStart_3337061 : Nat := 118140960795 + 3337061 * 2 ^ 59
def prefixEnd_3337061 : Nat := 4983230072969 + 3 ^ 40 * 3337061 * 2
def baseEnd_3337061 : Nat := 380781392527438548264587

theorem tailTrace_3337061 : CollatzResearch.WordTrace tailWord_3337061 prefixEnd_3337061 380781392527438548264587 := by
  unfold tailWord_3337061
  simp only [CollatzResearch.WordTrace]
  refine ⟨121712613763405396489891037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81141742508936930993260691 121712613763405396489891037)
  ·
    refine ⟨45642230161277023683709139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121712613763405396489891037 45642230161277023683709139)
    ·
      refine ⟨68463345241915535525563709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45642230161277023683709139 68463345241915535525563709)
      ·
        refine ⟨25673754465718325822086391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68463345241915535525563709 25673754465718325822086391)
        ·
          refine ⟨38510631698577488733129587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25673754465718325822086391 38510631698577488733129587)
          ·
            refine ⟨57765947547866233099694381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38510631698577488733129587 57765947547866233099694381)
            ·
              refine ⟨21662230330449837412385393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57765947547866233099694381 21662230330449837412385393)
              ·
                refine ⟨16246672747837378059289045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21662230330449837412385393 16246672747837378059289045)
                ·
                  refine ⟨380781392527438548264587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16246672747837378059289045 380781392527438548264587)
                  ·
                    rfl

theorem cell22_3337061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_3337061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337061 prefixEnd_3337061 := by exact prefixLift 3337061
  have htrace : WordTrace (prefixWord ++ tailWord_3337061) baseStart_3337061 baseEnd_3337061 := by
    simpa [prefixWord, tailWord_3337061, baseEnd_3337061] using wordTrace_append hprefix tailTrace_3337061
  have hstable : (prefixWord ++ tailWord_3337061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337061).length < 2 ^ (prefixWord ++ tailWord_3337061).sum := by decide
  have hdescent : baseEnd_3337061 < baseStart_3337061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337095 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 5]
def baseStart_3337095 : Nat := 118140960795 + 3337095 * 2 ^ 59
def prefixEnd_3337095 : Nat := 4983230072969 + 3 ^ 40 * 3337095 * 2
def baseEnd_3337095 : Nat := 380785272159050296481219

theorem tailTrace_3337095 : CollatzResearch.WordTrace tailWord_3337095 prefixEnd_3337095 380785272159050296481219 := by
  unfold tailWord_3337095
  simp only [CollatzResearch.WordTrace]
  refine ⟨121713853845282220296628739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81142569230188146864419159 121713853845282220296628739)
  ·
    refine ⟨182570780767923330444943109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121713853845282220296628739 182570780767923330444943109)
    ·
      refine ⟨34232021393985624458426833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182570780767923330444943109 34232021393985624458426833)
      ·
        refine ⟨25674016045489218343820125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34232021393985624458426833 25674016045489218343820125)
        ·
          refine ⟨9627756017058456878932547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25674016045489218343820125 9627756017058456878932547)
          ·
            refine ⟨14441634025587685318398821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9627756017058456878932547 14441634025587685318398821)
            ·
              refine ⟨2707806379797690997199779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14441634025587685318398821 2707806379797690997199779)
              ·
                refine ⟨4061709569696536495799669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707806379797690997199779 4061709569696536495799669)
                ·
                  refine ⟨380785272159050296481219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4061709569696536495799669 380785272159050296481219)
                  ·
                    rfl

theorem cell22_3337095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 5].length) (baseStart_3337095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337095 prefixEnd_3337095 := by exact prefixLift 3337095
  have htrace : WordTrace (prefixWord ++ tailWord_3337095) baseStart_3337095 baseEnd_3337095 := by
    simpa [prefixWord, tailWord_3337095, baseEnd_3337095] using wordTrace_append hprefix tailTrace_3337095
  have hstable : (prefixWord ++ tailWord_3337095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337095).length < 2 ^ (prefixWord ++ tailWord_3337095).sum := by decide
  have hdescent : baseEnd_3337095 < baseStart_3337095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337133 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3337133 : Nat := 118140960795 + 3337133 * 2 ^ 59
def prefixEnd_3337133 : Nat := 4983230072969 + 3 ^ 40 * 3337133 * 2
def baseEnd_3337133 : Nat := 1142368824653731456993541

theorem tailTrace_3337133 : CollatzResearch.WordTrace tailWord_3337133 prefixEnd_3337133 1142368824653731456993541 := by
  unfold tailWord_3337133
  simp only [CollatzResearch.WordTrace]
  refine ⟨121715239819144552786512053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81143493212763035191008035 121715239819144552786512053)
  ·
    refine ⟨11410803733044801823735505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121715239819144552786512053 11410803733044801823735505)
    ·
      refine ⟨8558102799783601367801629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11410803733044801823735505 8558102799783601367801629)
      ·
        refine ⟨3209288549918850512925611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8558102799783601367801629 3209288549918850512925611)
        ·
          refine ⟨4813932824878275769388417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209288549918850512925611 4813932824878275769388417)
          ·
            refine ⟨3610449618658706827041313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813932824878275769388417 3610449618658706827041313)
            ·
              refine ⟨2707837213994030120280985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610449618658706827041313 2707837213994030120280985)
              ·
                refine ⟨2030877910495522590210739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707837213994030120280985 2030877910495522590210739)
                ·
                  refine ⟨3046316865743283885316109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030877910495522590210739 3046316865743283885316109)
                  ·
                    refine ⟨1142368824653731456993541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046316865743283885316109 1142368824653731456993541)
                    ·
                      rfl

theorem cell22_3337133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3337133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337133 prefixEnd_3337133 := by exact prefixLift 3337133
  have htrace : WordTrace (prefixWord ++ tailWord_3337133) baseStart_3337133 baseEnd_3337133 := by
    simpa [prefixWord, tailWord_3337133, baseEnd_3337133] using wordTrace_append hprefix tailTrace_3337133
  have hstable : (prefixWord ++ tailWord_3337133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337133).length < 2 ^ (prefixWord ++ tailWord_3337133).sum := by decide
  have hdescent : baseEnd_3337133 < baseStart_3337133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337151 : List Nat := [1, 1, 2, 2, 2, 1, 2, 11]
def baseStart_3337151 : Nat := 118140960795 + 3337151 * 2 ^ 59
def prefixEnd_3337151 : Nat := 4983230072969 + 3 ^ 40 * 3337151 * 2
def baseEnd_3337151 : Nat := 126930554046842823338165

theorem tailTrace_3337151 : CollatzResearch.WordTrace tailWord_3337151 prefixEnd_3337151 126930554046842823338165 := by
  unfold tailWord_3337151
  simp only [CollatzResearch.WordTrace]
  refine ⟨121715896333079341860667307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81143930888719561240444871 121715896333079341860667307)
  ·
    refine ⟨182573844499619012791000961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121715896333079341860667307 182573844499619012791000961)
    ·
      refine ⟨136930383374714259593250721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182573844499619012791000961 136930383374714259593250721)
      ·
        refine ⟨102697787531035694694938041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136930383374714259593250721 102697787531035694694938041)
        ·
          refine ⟨77023340648276771021203531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102697787531035694694938041 77023340648276771021203531)
          ·
            refine ⟨115535010972415156531805297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77023340648276771021203531 115535010972415156531805297)
            ·
              refine ⟨86651258229311367398853973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115535010972415156531805297 86651258229311367398853973)
              ·
                refine ⟨126930554046842823338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 86651258229311367398853973 126930554046842823338165)
                ·
                  rfl

theorem cell22_3337151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 11].length) (baseStart_3337151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337151 prefixEnd_3337151 := by exact prefixLift 3337151
  have htrace : WordTrace (prefixWord ++ tailWord_3337151) baseStart_3337151 baseEnd_3337151 := by
    simpa [prefixWord, tailWord_3337151, baseEnd_3337151] using wordTrace_append hprefix tailTrace_3337151
  have hstable : (prefixWord ++ tailWord_3337151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337151).length < 2 ^ (prefixWord ++ tailWord_3337151).sum := by decide
  have hdescent : baseEnd_3337151 < baseStart_3337151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337170 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_3337170 : Nat := 118140960795 + 3337170 * 2 ^ 59
def prefixEnd_3337170 : Nat := 4983230072969 + 3 ^ 40 * 3337170 * 2
def baseEnd_3337170 : Nat := 1142381490509875693818427

theorem tailTrace_3337170 : CollatzResearch.WordTrace tailWord_3337170 prefixEnd_3337170 1142381490509875693818427 := by
  unfold tailWord_3337170
  simp only [CollatzResearch.WordTrace]
  refine ⟨30429147330002627026402241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81144392880007005403739309 30429147330002627026402241)
  ·
    refine ⟨22821860497501970269801681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30429147330002627026402241 22821860497501970269801681)
    ·
      refine ⟨17116395373126477702351261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22821860497501970269801681 17116395373126477702351261)
      ·
        refine ⟨6418648264922429138381723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17116395373126477702351261 6418648264922429138381723)
        ·
          refine ⟨9627972397383643707572585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418648264922429138381723 9627972397383643707572585)
          ·
            refine ⟨7220979298037732780679439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9627972397383643707572585 7220979298037732780679439)
            ·
              refine ⟨10831468947056599171019159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220979298037732780679439 10831468947056599171019159)
              ·
                refine ⟨16247203420584898756528739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831468947056599171019159 16247203420584898756528739)
                ·
                  refine ⟨24370805130877348134793109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16247203420584898756528739 24370805130877348134793109)
                  ·
                    refine ⟨1142381490509875693818427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24370805130877348134793109 1142381490509875693818427)
                    ·
                      rfl

theorem cell22_3337170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_3337170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337170 prefixEnd_3337170 := by exact prefixLift 3337170
  have htrace : WordTrace (prefixWord ++ tailWord_3337170) baseStart_3337170 baseEnd_3337170 := by
    simpa [prefixWord, tailWord_3337170, baseEnd_3337170] using wordTrace_append hprefix tailTrace_3337170
  have hstable : (prefixWord ++ tailWord_3337170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337170).length < 2 ^ (prefixWord ++ tailWord_3337170).sum := by decide
  have hdescent : baseEnd_3337170 < baseStart_3337170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337174 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3337174 : Nat := 118140960795 + 3337174 * 2 ^ 59
def prefixEnd_3337174 : Nat := 4983230072969 + 3 ^ 40 * 3337174 * 2
def baseEnd_3337174 : Nat := 380794286597207005572805

theorem tailTrace_3337174 : CollatzResearch.WordTrace tailWord_3337174 prefixEnd_3337174 380794286597207005572805 := by
  unfold tailWord_3337174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607295950749751049297161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81144490141330677859169717 7607295950749751049297161)
  ·
    refine ⟨5705471963062313286972871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7607295950749751049297161 5705471963062313286972871)
    ·
      refine ⟨8558207944593469930459307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705471963062313286972871 8558207944593469930459307)
      ·
        refine ⟨12837311916890204895688961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8558207944593469930459307 12837311916890204895688961)
        ·
          refine ⟨9627983937667653671766721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12837311916890204895688961 9627983937667653671766721)
          ·
            refine ⟨7220987953250740253825041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9627983937667653671766721 7220987953250740253825041)
            ·
              refine ⟨5415740964938055190368781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7220987953250740253825041 5415740964938055190368781)
              ·
                refine ⟨2030902861851770696388293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5415740964938055190368781 2030902861851770696388293)
                ·
                  refine ⟨380794286597207005572805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030902861851770696388293 380794286597207005572805)
                  ·
                    rfl

theorem cell22_3337174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3337174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337174 prefixEnd_3337174 := by exact prefixLift 3337174
  have htrace : WordTrace (prefixWord ++ tailWord_3337174) baseStart_3337174 baseEnd_3337174 := by
    simpa [prefixWord, tailWord_3337174, baseEnd_3337174] using wordTrace_append hprefix tailTrace_3337174
  have hstable : (prefixWord ++ tailWord_3337174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337174).length < 2 ^ (prefixWord ++ tailWord_3337174).sum := by decide
  have hdescent : baseEnd_3337174 < baseStart_3337174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337277 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_3337277 : Nat := 118140960795 + 3337277 * 2 ^ 59
def prefixEnd_3337277 : Nat := 4983230072969 + 3 ^ 40 * 3337277 * 2
def baseEnd_3337277 : Nat := 1142418118796563081393099

theorem tailTrace_3337277 : CollatzResearch.WordTrace tailWord_3337277 prefixEnd_3337277 1142418118796563081393099 := by
  unfold tailWord_3337277
  simp only [CollatzResearch.WordTrace]
  refine ⟨121720491930622865379754085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81146994620415243586502723 121720491930622865379754085)
  ·
    refine ⟨22822592236991787258703891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121720491930622865379754085 22822592236991787258703891)
    ·
      refine ⟨34233888355487680888055837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22822592236991787258703891 34233888355487680888055837)
      ·
        refine ⟨12837708133307880333020939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34233888355487680888055837 12837708133307880333020939)
        ·
          refine ⟨19256562199961820499531409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12837708133307880333020939 19256562199961820499531409)
          ·
            refine ⟨14442421649971365374648557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19256562199961820499531409 14442421649971365374648557)
            ·
              refine ⟨5415908118739262015493209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14442421649971365374648557 5415908118739262015493209)
              ·
                refine ⟨4061931089054446511619907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415908118739262015493209 4061931089054446511619907)
                ·
                  refine ⟨6092896633581669767429861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061931089054446511619907 6092896633581669767429861)
                  ·
                    refine ⟨1142418118796563081393099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6092896633581669767429861 1142418118796563081393099)
                    ·
                      rfl

theorem cell22_3337277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_3337277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337277 prefixEnd_3337277 := by exact prefixLift 3337277
  have htrace : WordTrace (prefixWord ++ tailWord_3337277) baseStart_3337277 baseEnd_3337277 := by
    simpa [prefixWord, tailWord_3337277, baseEnd_3337277] using wordTrace_append hprefix tailTrace_3337277
  have hstable : (prefixWord ++ tailWord_3337277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337277).length < 2 ^ (prefixWord ++ tailWord_3337277).sum := by decide
  have hdescent : baseEnd_3337277 < baseStart_3337277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337290 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_3337290 : Nat := 118140960795 + 3337290 * 2 ^ 59
def prefixEnd_3337290 : Nat := 4983230072969 + 3 ^ 40 * 3337290 * 2
def baseEnd_3337290 : Nat := 1142422568962235380818059

theorem tailTrace_3337290 : CollatzResearch.WordTrace tailWord_3337290 prefixEnd_3337290 1142422568962235380818059 := by
  unfold tailWord_3337290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30430241519893942149994331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81147310719717179066651549 30430241519893942149994331)
  ·
    refine ⟨45645362279840913224991497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30430241519893942149994331 45645362279840913224991497)
    ·
      refine ⟨34234021709880684918743623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45645362279840913224991497 34234021709880684918743623)
      ·
        refine ⟨51351032564821027378115435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34234021709880684918743623 51351032564821027378115435)
        ·
          refine ⟨77026548847231541067173153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51351032564821027378115435 77026548847231541067173153)
          ·
            refine ⟨57769911635423655800379865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77026548847231541067173153 57769911635423655800379865)
            ·
              refine ⟨43327433726567741850284899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57769911635423655800379865 43327433726567741850284899)
              ·
                refine ⟨64991150589851612775427349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43327433726567741850284899 64991150589851612775427349)
                ·
                  refine ⟨3046460183899294348848157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64991150589851612775427349 3046460183899294348848157)
                  ·
                    refine ⟨1142422568962235380818059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046460183899294348848157 1142422568962235380818059)
                    ·
                      rfl

theorem cell22_3337290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_3337290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337290 prefixEnd_3337290 := by exact prefixLift 3337290
  have htrace : WordTrace (prefixWord ++ tailWord_3337290) baseStart_3337290 baseEnd_3337290 := by
    simpa [prefixWord, tailWord_3337290, baseEnd_3337290] using wordTrace_append hprefix tailTrace_3337290
  have hstable : (prefixWord ++ tailWord_3337290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337290).length < 2 ^ (prefixWord ++ tailWord_3337290).sum := by decide
  have hdescent : baseEnd_3337290 < baseStart_3337290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337302 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3337302 : Nat := 118140960795 + 3337302 * 2 ^ 59
def prefixEnd_3337302 : Nat := 4983230072969 + 3 ^ 40 * 3337302 * 2
def baseEnd_3337302 : Nat := 1142426676807471349518023

theorem tailTrace_3337302 : CollatzResearch.WordTrace tailWord_3337302 prefixEnd_3337302 1142426676807471349518023 := by
  unfold tailWord_3337302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607587734720768415588385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81147602503688196432942773 7607587734720768415588385)
  ·
    refine ⟨5705690801040576311691289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7607587734720768415588385 5705690801040576311691289)
    ·
      refine ⟨4279268100780432233768467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5705690801040576311691289 4279268100780432233768467)
      ·
        refine ⟨6418902151170648350652701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279268100780432233768467 6418902151170648350652701)
        ·
          refine ⟨2407088306688993131494763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6418902151170648350652701 2407088306688993131494763)
          ·
            refine ⟨3610632460033489697242145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407088306688993131494763 3610632460033489697242145)
            ·
              refine ⟨2707974345025117272931609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610632460033489697242145 2707974345025117272931609)
              ·
                refine ⟨2030980758768837954698707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707974345025117272931609 2030980758768837954698707)
                ·
                  refine ⟨3046471138153256932048061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030980758768837954698707 3046471138153256932048061)
                  ·
                    refine ⟨1142426676807471349518023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046471138153256932048061 1142426676807471349518023)
                    ·
                      rfl

theorem cell22_3337302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3337302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337302 prefixEnd_3337302 := by exact prefixLift 3337302
  have htrace : WordTrace (prefixWord ++ tailWord_3337302) baseStart_3337302 baseEnd_3337302 := by
    simpa [prefixWord, tailWord_3337302, baseEnd_3337302] using wordTrace_append hprefix tailTrace_3337302
  have hstable : (prefixWord ++ tailWord_3337302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337302).length < 2 ^ (prefixWord ++ tailWord_3337302).sum := by decide
  have hdescent : baseEnd_3337302 < baseStart_3337302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337337 : List Nat := [1, 2, 1, 3, 5, 1, 3, 6]
def baseStart_3337337 : Nat := 118140960795 + 3337337 * 2 ^ 59
def prefixEnd_3337337 : Nat := 4983230072969 + 3 ^ 40 * 3337337 * 2
def baseEnd_3337337 : Nat := 126937628669193658321435

theorem tailTrace_3337337 : CollatzResearch.WordTrace tailWord_3337337 prefixEnd_3337337 126937628669193658321435 := by
  unfold tailWord_3337337
  simp only [CollatzResearch.WordTrace]
  refine ⟨121722680310405495626938265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81148453540270330417958843 121722680310405495626938265)
  ·
    refine ⟨91292010232804121720203699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121722680310405495626938265 91292010232804121720203699)
    ·
      refine ⟨136938015349206182580305549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91292010232804121720203699 136938015349206182580305549)
      ·
        refine ⟨51351755755952318467614581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136938015349206182580305549 51351755755952318467614581)
        ·
          refine ⟨4814227102120529856338867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51351755755952318467614581 4814227102120529856338867)
          ·
            refine ⟨7221340653180794784508301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814227102120529856338867 7221340653180794784508301)
            ·
              refine ⟨2708002744942798044190613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7221340653180794784508301 2708002744942798044190613)
              ·
                refine ⟨126937628669193658321435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2708002744942798044190613 126937628669193658321435)
                ·
                  rfl

theorem cell22_3337337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 6].length) (baseStart_3337337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337337 prefixEnd_3337337 := by exact prefixLift 3337337
  have htrace : WordTrace (prefixWord ++ tailWord_3337337) baseStart_3337337 baseEnd_3337337 := by
    simpa [prefixWord, tailWord_3337337, baseEnd_3337337] using wordTrace_append hprefix tailTrace_3337337
  have hstable : (prefixWord ++ tailWord_3337337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337337).length < 2 ^ (prefixWord ++ tailWord_3337337).sum := by decide
  have hdescent : baseEnd_3337337 < baseStart_3337337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337365 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 5]
def baseStart_3337365 : Nat := 118140960795 + 3337365 * 2 ^ 59
def prefixEnd_3337365 : Nat := 4983230072969 + 3 ^ 40 * 3337365 * 2
def baseEnd_3337365 : Nat := 380816080998320061730943

theorem tailTrace_3337365 : CollatzResearch.WordTrace tailWord_3337365 prefixEnd_3337365 380816080998320061730943 := by
  unfold tailWord_3337365
  simp only [CollatzResearch.WordTrace]
  refine ⟨121723701554304056408957549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81149134369536037605971699 121723701554304056408957549)
  ·
    refine ⟨45646388082864021153359081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121723701554304056408957549 45646388082864021153359081)
    ·
      refine ⟨34234791062148015865019311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45646388082864021153359081 34234791062148015865019311)
      ·
        refine ⟨51352186593222023797528967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34234791062148015865019311 51352186593222023797528967)
        ·
          refine ⟨77028279889833035696293451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51352186593222023797528967 77028279889833035696293451)
          ·
            refine ⟨115542419834749553544440177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77028279889833035696293451 115542419834749553544440177)
            ·
              refine ⟨86656814876062165158330133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115542419834749553544440177 86656814876062165158330133)
              ·
                refine ⟨4062038197315413991796725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86656814876062165158330133 4062038197315413991796725)
                ·
                  refine ⟨380816080998320061730943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4062038197315413991796725 380816080998320061730943)
                  ·
                    rfl

theorem cell22_3337365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_3337365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337365 prefixEnd_3337365 := by exact prefixLift 3337365
  have htrace : WordTrace (prefixWord ++ tailWord_3337365) baseStart_3337365 baseEnd_3337365 := by
    simpa [prefixWord, tailWord_3337365, baseEnd_3337365] using wordTrace_append hprefix tailTrace_3337365
  have hstable : (prefixWord ++ tailWord_3337365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337365).length < 2 ^ (prefixWord ++ tailWord_3337365).sum := by decide
  have hdescent : baseEnd_3337365 < baseStart_3337365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337395 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 3, 4]
def baseStart_3337395 : Nat := 118140960795 + 3337395 * 2 ^ 59
def prefixEnd_3337395 : Nat := 4983230072969 + 3 ^ 40 * 3337395 * 2
def baseEnd_3337395 : Nat := 1142458512608050106942737

theorem tailTrace_3337395 : CollatzResearch.WordTrace tailWord_3337395 prefixEnd_3337395 1142458512608050106942737 := by
  unfold tailWord_3337395
  simp only [CollatzResearch.WordTrace]
  refine ⟨121724795744195371532549639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81149863829463581021699759 121724795744195371532549639)
  ·
    refine ⟨182587193616293057298824459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121724795744195371532549639 182587193616293057298824459)
    ·
      refine ⟨273880790424439585948236689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182587193616293057298824459 273880790424439585948236689)
      ·
        refine ⟨205410592818329689461177517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273880790424439585948236689 205410592818329689461177517)
        ·
          refine ⟨77028972306873633547941569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205410592818329689461177517 77028972306873633547941569)
          ·
            refine ⟨57771729230155225160956177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77028972306873633547941569 57771729230155225160956177)
            ·
              refine ⟨43328796922616418870717133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57771729230155225160956177 43328796922616418870717133)
              ·
                refine ⟨16248298845981157076518925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43328796922616418870717133 16248298845981157076518925)
                ·
                  refine ⟨6093112067242933903694597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16248298845981157076518925 6093112067242933903694597)
                  ·
                    refine ⟨1142458512608050106942737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6093112067242933903694597 1142458512608050106942737)
                    ·
                      rfl

theorem cell22_3337395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_3337395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337395 prefixEnd_3337395 := by exact prefixLift 3337395
  have htrace : WordTrace (prefixWord ++ tailWord_3337395) baseStart_3337395 baseEnd_3337395 := by
    simpa [prefixWord, tailWord_3337395, baseEnd_3337395] using wordTrace_append hprefix tailTrace_3337395
  have hstable : (prefixWord ++ tailWord_3337395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337395).length < 2 ^ (prefixWord ++ tailWord_3337395).sum := by decide
  have hdescent : baseEnd_3337395 < baseStart_3337395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337476 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_3337476 : Nat := 118140960795 + 3337476 * 2 ^ 59
def prefixEnd_3337476 : Nat := 4983230072969 + 3 ^ 40 * 3337476 * 2
def baseEnd_3337476 : Nat := 1142486240563392895667489

theorem tailTrace_3337476 : CollatzResearch.WordTrace tailWord_3337476 prefixEnd_3337476 1142486240563392895667489 := by
  unfold tailWord_3337476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60863875028450961183124141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81151833371267948244165521 60863875028450961183124141)
  ·
    refine ⟨22823953135669110443671553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60863875028450961183124141 22823953135669110443671553)
    ·
      refine ⟨17117964851751832832753665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22823953135669110443671553 17117964851751832832753665)
      ·
        refine ⟨12838473638813874624565249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17117964851751832832753665 12838473638813874624565249)
        ·
          refine ⟨9628855229110405968423937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12838473638813874624565249 9628855229110405968423937)
          ·
            refine ⟨7221641421832804476317953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9628855229110405968423937 7221641421832804476317953)
            ·
              refine ⟨5416231066374603357238465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221641421832804476317953 5416231066374603357238465)
              ·
                refine ⟨4062173299780952517928849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416231066374603357238465 4062173299780952517928849)
                ·
                  refine ⟨3046629974835714388446637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4062173299780952517928849 3046629974835714388446637)
                  ·
                    refine ⟨1142486240563392895667489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046629974835714388446637 1142486240563392895667489)
                    ·
                      rfl

theorem cell22_3337476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_3337476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337476 prefixEnd_3337476 := by exact prefixLift 3337476
  have htrace : WordTrace (prefixWord ++ tailWord_3337476) baseStart_3337476 baseEnd_3337476 := by
    simpa [prefixWord, tailWord_3337476, baseEnd_3337476] using wordTrace_append hprefix tailTrace_3337476
  have hstable : (prefixWord ++ tailWord_3337476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337476).length < 2 ^ (prefixWord ++ tailWord_3337476).sum := by decide
  have hdescent : baseEnd_3337476 < baseStart_3337476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337521 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 1, 3]
def baseStart_3337521 : Nat := 118140960795 + 3337521 * 2 ^ 59
def prefixEnd_3337521 : Nat := 4983230072969 + 3 ^ 40 * 3337521 * 2
def baseEnd_3337521 : Nat := 1142501644983027778292351

theorem tailTrace_3337521 : CollatzResearch.WordTrace tailWord_3337521 prefixEnd_3337521 1142501644983027778292351 := by
  unfold tailWord_3337521
  simp only [CollatzResearch.WordTrace]
  refine ⟨121729391341738895051636417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81152927561159263367757611 121729391341738895051636417)
  ·
    refine ⟨91297043506304171288727313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121729391341738895051636417 91297043506304171288727313)
    ·
      refine ⟨68472782629728128466545485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91297043506304171288727313 68472782629728128466545485)
      ·
        refine ⟨25677293486148048174954557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68472782629728128466545485 25677293486148048174954557)
        ·
          refine ⟨9628985057305518065607959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25677293486148048174954557 9628985057305518065607959)
          ·
            refine ⟨14443477585958277098411939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628985057305518065607959 14443477585958277098411939)
            ·
              refine ⟨21665216378937415647617909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14443477585958277098411939 21665216378937415647617909)
              ·
                refine ⟨2031114035525382716964179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21665216378937415647617909 2031114035525382716964179)
                ·
                  refine ⟨3046671053288074075446269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031114035525382716964179 3046671053288074075446269)
                  ·
                    refine ⟨1142501644983027778292351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046671053288074075446269 1142501644983027778292351)
                    ·
                      rfl

theorem cell22_3337521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_3337521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337521 prefixEnd_3337521 := by exact prefixLift 3337521
  have htrace : WordTrace (prefixWord ++ tailWord_3337521) baseStart_3337521 baseEnd_3337521 := by
    simpa [prefixWord, tailWord_3337521, baseEnd_3337521] using wordTrace_append hprefix tailTrace_3337521
  have hstable : (prefixWord ++ tailWord_3337521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337521).length < 2 ^ (prefixWord ++ tailWord_3337521).sum := by decide
  have hdescent : baseEnd_3337521 < baseStart_3337521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337532 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3337532 : Nat := 118140960795 + 3337532 * 2 ^ 59
def prefixEnd_3337532 : Nat := 4983230072969 + 3 ^ 40 * 3337532 * 2
def baseEnd_3337532 : Nat := 1142505410507827416267317

theorem tailTrace_3337532 : CollatzResearch.WordTrace tailWord_3337532 prefixEnd_3337532 1142505410507827416267317 := by
  unfold tailWord_3337532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60864896272349521965143425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81153195029799362620191233 60864896272349521965143425)
  ·
    refine ⟨45648672204262141473857569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60864896272349521965143425 45648672204262141473857569)
    ·
      refine ⟨34236504153196606105393177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45648672204262141473857569 34236504153196606105393177)
      ·
        refine ⟨25677378114897454579044883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34236504153196606105393177 25677378114897454579044883)
        ·
          refine ⟨38516067172346181868567325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25677378114897454579044883 38516067172346181868567325)
          ·
            refine ⟨14443525189629818200712747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38516067172346181868567325 14443525189629818200712747)
            ·
              refine ⟨21665287784444727301069121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14443525189629818200712747 21665287784444727301069121)
              ·
                refine ⟨16248965838333545475801841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21665287784444727301069121 16248965838333545475801841)
                ·
                  refine ⟨12186724378750159106851381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16248965838333545475801841 12186724378750159106851381)
                  ·
                    refine ⟨1142505410507827416267317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12186724378750159106851381 1142505410507827416267317)
                    ·
                      rfl

theorem cell22_3337532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3337532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337532 prefixEnd_3337532 := by exact prefixLift 3337532
  have htrace : WordTrace (prefixWord ++ tailWord_3337532) baseStart_3337532 baseEnd_3337532 := by
    simpa [prefixWord, tailWord_3337532, baseEnd_3337532] using wordTrace_append hprefix tailTrace_3337532
  have hstable : (prefixWord ++ tailWord_3337532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337532).length < 2 ^ (prefixWord ++ tailWord_3337532).sum := by decide
  have hdescent : baseEnd_3337532 < baseStart_3337532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337562 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_3337562 : Nat := 118140960795 + 3337562 * 2 ^ 59
def prefixEnd_3337562 : Nat := 4983230072969 + 3 ^ 40 * 3337562 * 2
def baseEnd_3337562 : Nat := 380838560040305779339075

theorem tailTrace_3337562 : CollatzResearch.WordTrace tailWord_3337562 prefixEnd_3337562 380838560040305779339075 := by
  unfold tailWord_3337562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30432721683647589763469735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81153924489726906035919293 30432721683647589763469735)
  ·
    refine ⟨45649082525471384645204603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30432721683647589763469735 45649082525471384645204603)
    ·
      refine ⟨68473623788207076967806905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45649082525471384645204603 68473623788207076967806905)
      ·
        refine ⟨51355217841155307725855179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68473623788207076967806905 51355217841155307725855179)
        ·
          refine ⟨77032826761732961588782769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51355217841155307725855179 77032826761732961588782769)
          ·
            refine ⟨57774620071299721191587077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77032826761732961588782769 57774620071299721191587077)
            ·
              refine ⟨10832741263368697723422577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57774620071299721191587077 10832741263368697723422577)
              ·
                refine ⟨8124555947526523292566933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10832741263368697723422577 8124555947526523292566933)
                ·
                  refine ⟨380838560040305779339075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8124555947526523292566933 380838560040305779339075)
                  ·
                    rfl

theorem cell22_3337562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_3337562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337562 prefixEnd_3337562 := by exact prefixLift 3337562
  have htrace : WordTrace (prefixWord ++ tailWord_3337562) baseStart_3337562 baseEnd_3337562 := by
    simpa [prefixWord, tailWord_3337562, baseEnd_3337562] using wordTrace_append hprefix tailTrace_3337562
  have hstable : (prefixWord ++ tailWord_3337562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337562).length < 2 ^ (prefixWord ++ tailWord_3337562).sum := by decide
  have hdescent : baseEnd_3337562 < baseStart_3337562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337596 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 4]
def baseStart_3337596 : Nat := 118140960795 + 3337596 * 2 ^ 59
def prefixEnd_3337596 : Nat := 4983230072969 + 3 ^ 40 * 3337596 * 2
def baseEnd_3337596 : Nat := 380842439671917527555707

theorem tailTrace_3337596 : CollatzResearch.WordTrace tailWord_3337596 prefixEnd_3337596 380842439671917527555707 := by
  unfold tailWord_3337596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60866063408233591430308321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81154751210978121907077761 60866063408233591430308321)
  ·
    refine ⟨45649547556175193572731241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60866063408233591430308321 45649547556175193572731241)
    ·
      refine ⟨34237160667131395179548431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45649547556175193572731241 34237160667131395179548431)
      ·
        refine ⟨51355741000697092769322647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34237160667131395179548431 51355741000697092769322647)
        ·
          refine ⟨77033611501045639153983971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51355741000697092769322647 77033611501045639153983971)
          ·
            refine ⟨115550417251568458730975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77033611501045639153983971 115550417251568458730975957)
            ·
              refine ⟨2708212904333635751507249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 115550417251568458730975957 2708212904333635751507249)
              ·
                refine ⟨2031159678250226813630437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708212904333635751507249 2031159678250226813630437)
                ·
                  refine ⟨380842439671917527555707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031159678250226813630437 380842439671917527555707)
                  ·
                    rfl

theorem cell22_3337596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_3337596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337596 prefixEnd_3337596 := by exact prefixLift 3337596
  have htrace : WordTrace (prefixWord ++ tailWord_3337596) baseStart_3337596 baseEnd_3337596 := by
    simpa [prefixWord, tailWord_3337596, baseEnd_3337596] using wordTrace_append hprefix tailTrace_3337596
  have hstable : (prefixWord ++ tailWord_3337596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337596).length < 2 ^ (prefixWord ++ tailWord_3337596).sum := by decide
  have hdescent : baseEnd_3337596 < baseStart_3337596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337607 : List Nat := [1, 1, 4, 2, 2, 2, 1, 9]
def baseStart_3337607 : Nat := 118140960795 + 3337607 * 2 ^ 59
def prefixEnd_3337607 : Nat := 4983230072969 + 3 ^ 40 * 3337607 * 2
def baseEnd_3337607 : Nat := 126947898282283580071343

theorem tailTrace_3337607 : CollatzResearch.WordTrace tailWord_3337607 prefixEnd_3337607 126947898282283580071343 := by
  unfold tailWord_3337607
  simp only [CollatzResearch.WordTrace]
  refine ⟨121732528019427331739267075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81155018679618221159511383 121732528019427331739267075)
  ·
    refine ⟨182598792029140997608900613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121732528019427331739267075 182598792029140997608900613)
    ·
      refine ⟨34237273505463937051668865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182598792029140997608900613 34237273505463937051668865)
      ·
        refine ⟨25677955129097952788751649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34237273505463937051668865 25677955129097952788751649)
        ·
          refine ⟨19258466346823464591563737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25677955129097952788751649 19258466346823464591563737)
          ·
            refine ⟨14443849760117598443672803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19258466346823464591563737 14443849760117598443672803)
            ·
              refine ⟨21665774640176397665509205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14443849760117598443672803 21665774640176397665509205)
              ·
                refine ⟨126947898282283580071343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21665774640176397665509205 126947898282283580071343)
                ·
                  rfl

theorem cell22_3337607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 9].length) (baseStart_3337607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337607 prefixEnd_3337607 := by exact prefixLift 3337607
  have htrace : WordTrace (prefixWord ++ tailWord_3337607) baseStart_3337607 baseEnd_3337607 := by
    simpa [prefixWord, tailWord_3337607, baseEnd_3337607] using wordTrace_append hprefix tailTrace_3337607
  have hstable : (prefixWord ++ tailWord_3337607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337607).length < 2 ^ (prefixWord ++ tailWord_3337607).sum := by decide
  have hdescent : baseEnd_3337607 < baseStart_3337607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337667 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_3337667 : Nat := 118140960795 + 3337667 * 2 ^ 59
def prefixEnd_3337667 : Nat := 4983230072969 + 3 ^ 40 * 3337667 * 2
def baseEnd_3337667 : Nat := 1142551623766732064141903

theorem tailTrace_3337667 : CollatzResearch.WordTrace tailWord_3337667 prefixEnd_3337667 1142551623766732064141903 := by
  unfold tailWord_3337667
  simp only [CollatzResearch.WordTrace]
  refine ⟨121734716399209961986451255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81156477599473307990967503 121734716399209961986451255)
  ·
    refine ⟨182602074598814942979676883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121734716399209961986451255 182602074598814942979676883)
    ·
      refine ⟨273903111898222414469515325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182602074598814942979676883 273903111898222414469515325)
      ·
        refine ⟨102713666961833405426068247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273903111898222414469515325 102713666961833405426068247)
        ·
          refine ⟨154070500442750108139102371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102713666961833405426068247 154070500442750108139102371)
          ·
            refine ⟨231105750664125162208653557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154070500442750108139102371 231105750664125162208653557)
            ·
              refine ⟨21666164124761733957061271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231105750664125162208653557 21666164124761733957061271)
              ·
                refine ⟨32499246187142600935591907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21666164124761733957061271 32499246187142600935591907)
                ·
                  refine ⟨48748869280713901403387861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32499246187142600935591907 48748869280713901403387861)
                  ·
                    refine ⟨1142551623766732064141903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48748869280713901403387861 1142551623766732064141903)
                    ·
                      rfl

theorem cell22_3337667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_3337667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337667 prefixEnd_3337667 := by exact prefixLift 3337667
  have htrace : WordTrace (prefixWord ++ tailWord_3337667) baseStart_3337667 baseEnd_3337667 := by
    simpa [prefixWord, tailWord_3337667, baseEnd_3337667] using wordTrace_append hprefix tailTrace_3337667
  have hstable : (prefixWord ++ tailWord_3337667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337667).length < 2 ^ (prefixWord ++ tailWord_3337667).sum := by decide
  have hdescent : baseEnd_3337667 < baseStart_3337667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337741 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3337741 : Nat := 118140960795 + 3337741 * 2 ^ 59
def prefixEnd_3337741 : Nat := 4983230072969 + 3 ^ 40 * 3337741 * 2
def baseEnd_3337741 : Nat := 1142576955479020537791677

theorem tailTrace_3337741 : CollatzResearch.WordTrace tailWord_3337741 prefixEnd_3337741 1142576955479020537791677 := by
  unfold tailWord_3337741
  simp only [CollatzResearch.WordTrace]
  refine ⟨121737415400941872624645077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81158276933961248416430051 121737415400941872624645077)
  ·
    refine ⟨2853220673459575139640119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 121737415400941872624645077 2853220673459575139640119)
    ·
      refine ⟨4279831010189362709460179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853220673459575139640119 4279831010189362709460179)
      ·
        refine ⟨6419746515284044064190269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279831010189362709460179 6419746515284044064190269)
        ·
          refine ⟨2407404943231516524071351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6419746515284044064190269 2407404943231516524071351)
          ·
            refine ⟨3611107414847274786107027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407404943231516524071351 3611107414847274786107027)
            ·
              refine ⟨5416661122270912179160541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611107414847274786107027 5416661122270912179160541)
              ·
                refine ⟨2031247920851592067185203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5416661122270912179160541 2031247920851592067185203)
                ·
                  refine ⟨3046871881277388100777805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031247920851592067185203 3046871881277388100777805)
                  ·
                    refine ⟨1142576955479020537791677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046871881277388100777805 1142576955479020537791677)
                    ·
                      rfl

theorem cell22_3337741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3337741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337741 prefixEnd_3337741 := by exact prefixLift 3337741
  have htrace : WordTrace (prefixWord ++ tailWord_3337741) baseStart_3337741 baseEnd_3337741 := by
    simpa [prefixWord, tailWord_3337741, baseEnd_3337741] using wordTrace_append hprefix tailTrace_3337741
  have hstable : (prefixWord ++ tailWord_3337741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337741).length < 2 ^ (prefixWord ++ tailWord_3337741).sum := by decide
  have hdescent : baseEnd_3337741 < baseStart_3337741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337761 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3337761 : Nat := 118140960795 + 3337761 * 2 ^ 59
def prefixEnd_3337761 : Nat := 4983230072969 + 3 ^ 40 * 3337761 * 2
def baseEnd_3337761 : Nat := 1142583801887747152291615

theorem tailTrace_3337761 : CollatzResearch.WordTrace tailWord_3337761 prefixEnd_3337761 1142583801887747152291615 := by
  unfold tailWord_3337761
  simp only [CollatzResearch.WordTrace]
  refine ⟨121738144860869416040373137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81158763240579610693582091 121738144860869416040373137)
  ·
    refine ⟨91303608645652062030279853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121738144860869416040373137 91303608645652062030279853)
    ·
      refine ⟨34238853242119523261354945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91303608645652062030279853 34238853242119523261354945)
      ·
        refine ⟨25679139931589642446016209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34238853242119523261354945 25679139931589642446016209)
        ·
          refine ⟨19259354948692231834512157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25679139931589642446016209 19259354948692231834512157)
          ·
            refine ⟨7222258105759586937942059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19259354948692231834512157 7222258105759586937942059)
            ·
              refine ⟨10833387158639380406913089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222258105759586937942059 10833387158639380406913089)
              ·
                refine ⟨8125040368979535305184817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10833387158639380406913089 8125040368979535305184817)
                ·
                  refine ⟨6093780276734651478888613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8125040368979535305184817 6093780276734651478888613)
                  ·
                    refine ⟨1142583801887747152291615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6093780276734651478888613 1142583801887747152291615)
                    ·
                      rfl

theorem cell22_3337761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3337761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337761 prefixEnd_3337761 := by exact prefixLift 3337761
  have htrace : WordTrace (prefixWord ++ tailWord_3337761) baseStart_3337761 baseEnd_3337761 := by
    simpa [prefixWord, tailWord_3337761, baseEnd_3337761] using wordTrace_append hprefix tailTrace_3337761
  have hstable : (prefixWord ++ tailWord_3337761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337761).length < 2 ^ (prefixWord ++ tailWord_3337761).sum := by decide
  have hdescent : baseEnd_3337761 < baseStart_3337761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337808 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 1, 3]
def baseStart_3337808 : Nat := 118140960795 + 3337808 * 2 ^ 59
def prefixEnd_3337808 : Nat := 4983230072969 + 3 ^ 40 * 3337808 * 2
def baseEnd_3337808 : Nat := 1142599890948254696366471

theorem tailTrace_3337808 : CollatzResearch.WordTrace tailWord_3337808 prefixEnd_3337808 1142599890948254696366471 := by
  unfold tailWord_3337808
  simp only [CollatzResearch.WordTrace]
  refine ⟨60869929545849571533667039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81159906061132762044889385 60869929545849571533667039)
  ·
    refine ⟨91304894318774357300500559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60869929545849571533667039 91304894318774357300500559)
    ·
      refine ⟨136957341478161535950750839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91304894318774357300500559 136957341478161535950750839)
      ·
        refine ⟨205436012217242303926126259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136957341478161535950750839 205436012217242303926126259)
        ·
          refine ⟨308154018325863455889189389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205436012217242303926126259 308154018325863455889189389)
          ·
            refine ⟨115557756872198795958446021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308154018325863455889189389 115557756872198795958446021)
            ·
              refine ⟨21667079413537274242208629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115557756872198795958446021 21667079413537274242208629)
              ·
                refine ⟨2031288695019119460207059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21667079413537274242208629 2031288695019119460207059)
                ·
                  refine ⟨3046933042528679190310589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031288695019119460207059 3046933042528679190310589)
                  ·
                    refine ⟨1142599890948254696366471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046933042528679190310589 1142599890948254696366471)
                    ·
                      rfl

theorem cell22_3337808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_3337808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337808 prefixEnd_3337808 := by exact prefixLift 3337808
  have htrace : WordTrace (prefixWord ++ tailWord_3337808) baseStart_3337808 baseEnd_3337808 := by
    simpa [prefixWord, tailWord_3337808, baseEnd_3337808] using wordTrace_append hprefix tailTrace_3337808
  have hstable : (prefixWord ++ tailWord_3337808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337808).length < 2 ^ (prefixWord ++ tailWord_3337808).sum := by decide
  have hdescent : baseEnd_3337808 < baseStart_3337808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337814 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3337814 : Nat := 118140960795 + 3337814 * 2 ^ 59
def prefixEnd_3337814 : Nat := 4983230072969 + 3 ^ 40 * 3337814 * 2
def baseEnd_3337814 : Nat := 1142601944870872680716453

theorem tailTrace_3337814 : CollatzResearch.WordTrace tailWord_3337814 prefixEnd_3337814 1142601944870872680716453 := by
  unfold tailWord_3337814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608754870604837880753281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81160051953118270728034997 7608754870604837880753281)
  ·
    refine ⟨5706566152953628410564961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7608754870604837880753281 5706566152953628410564961)
    ·
      refine ⟨4279924614715221307923721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5706566152953628410564961 4279924614715221307923721)
      ·
        refine ⟨3209943461036415980942791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4279924614715221307923721 3209943461036415980942791)
        ·
          refine ⟨4814915191554623971414187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209943461036415980942791 4814915191554623971414187)
          ·
            refine ⟨7222372787331935957121281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814915191554623971414187 7222372787331935957121281)
            ·
              refine ⟨5416779590498951967840961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7222372787331935957121281 5416779590498951967840961)
              ·
                refine ⟨4062584692874213975880721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416779590498951967840961 4062584692874213975880721)
                ·
                  refine ⟨3046938519655660481910541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4062584692874213975880721 3046938519655660481910541)
                  ·
                    refine ⟨1142601944870872680716453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3046938519655660481910541 1142601944870872680716453)
                    ·
                      rfl

theorem cell22_3337814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3337814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337814 prefixEnd_3337814 := by exact prefixLift 3337814
  have htrace : WordTrace (prefixWord ++ tailWord_3337814) baseStart_3337814 baseEnd_3337814 := by
    simpa [prefixWord, tailWord_3337814, baseEnd_3337814] using wordTrace_append hprefix tailTrace_3337814
  have hstable : (prefixWord ++ tailWord_3337814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337814).length < 2 ^ (prefixWord ++ tailWord_3337814).sum := by decide
  have hdescent : baseEnd_3337814 < baseStart_3337814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337851 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 1, 4]
def baseStart_3337851 : Nat := 118140960795 + 3337851 * 2 ^ 59
def prefixEnd_3337851 : Nat := 4983230072969 + 3 ^ 40 * 3337851 * 2
def baseEnd_3337851 : Nat := 1142614610727016917541339

theorem tailTrace_3337851 : CollatzResearch.WordTrace tailWord_3337851 prefixEnd_3337851 1142614610727016917541339 := by
  unfold tailWord_3337851
  simp only [CollatzResearch.WordTrace]
  refine ⟨121741427430543361411149407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81160951620362240940766271 121741427430543361411149407)
  ·
    refine ⟨182612141145815042116724111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121741427430543361411149407 182612141145815042116724111)
    ·
      refine ⟨273918211718722563175086167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182612141145815042116724111 273918211718722563175086167)
      ·
        refine ⟨410877317578083844762629251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273918211718722563175086167 410877317578083844762629251)
        ·
          refine ⟨616315976367125767143943877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410877317578083844762629251 616315976367125767143943877)
          ·
            refine ⟨115559245568836081339489477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 616315976367125767143943877 115559245568836081339489477)
            ·
              refine ⟨21667358544156765251154277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115559245568836081339489477 21667358544156765251154277)
              ·
                refine ⟨4062629727029393484591427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21667358544156765251154277 4062629727029393484591427)
                ·
                  refine ⟨6093944590544090226887141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062629727029393484591427 6093944590544090226887141)
                  ·
                    refine ⟨1142614610727016917541339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6093944590544090226887141 1142614610727016917541339)
                    ·
                      rfl

theorem cell22_3337851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4].length) (baseStart_3337851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337851 prefixEnd_3337851 := by exact prefixLift 3337851
  have htrace : WordTrace (prefixWord ++ tailWord_3337851) baseStart_3337851 baseEnd_3337851 := by
    simpa [prefixWord, tailWord_3337851, baseEnd_3337851] using wordTrace_append hprefix tailTrace_3337851
  have hstable : (prefixWord ++ tailWord_3337851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337851).length < 2 ^ (prefixWord ++ tailWord_3337851).sum := by decide
  have hdescent : baseEnd_3337851 < baseStart_3337851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337902 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3337902 : Nat := 118140960795 + 3337902 * 2 ^ 59
def prefixEnd_3337902 : Nat := 4983230072969 + 3 ^ 40 * 3337902 * 2
def baseEnd_3337902 : Nat := 1142632069069269784516183

theorem tailTrace_3337902 : CollatzResearch.WordTrace tailWord_3337902 prefixEnd_3337902 1142632069069269784516183 := by
  unfold tailWord_3337902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15217910944169824640156995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81162191702239064747503973 15217910944169824640156995)
  ·
    refine ⟨22826866416254736960235493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15217910944169824640156995 22826866416254736960235493)
    ·
      refine ⟨4280037453047763180044155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22826866416254736960235493 4280037453047763180044155)
      ·
        refine ⟨6420056179571644770066233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280037453047763180044155 6420056179571644770066233)
        ·
          refine ⟨4815042134678733577549675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6420056179571644770066233 4815042134678733577549675)
          ·
            refine ⟨7222563202018100366324513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815042134678733577549675 7222563202018100366324513)
            ·
              refine ⟨5416922401513575274743385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7222563202018100366324513 5416922401513575274743385)
              ·
                refine ⟨4062691801135181456057539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416922401513575274743385 4062691801135181456057539)
                ·
                  refine ⟨6094037701702772184086309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062691801135181456057539 6094037701702772184086309)
                  ·
                    refine ⟨1142632069069269784516183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094037701702772184086309 1142632069069269784516183)
                    ·
                      rfl

theorem cell22_3337902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3337902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337902 prefixEnd_3337902 := by exact prefixLift 3337902
  have htrace : WordTrace (prefixWord ++ tailWord_3337902) baseStart_3337902 baseEnd_3337902 := by
    simpa [prefixWord, tailWord_3337902, baseEnd_3337902] using wordTrace_append hprefix tailTrace_3337902
  have hstable : (prefixWord ++ tailWord_3337902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337902).length < 2 ^ (prefixWord ++ tailWord_3337902).sum := by decide
  have hdescent : baseEnd_3337902 < baseStart_3337902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337911 : List Nat := [1, 1, 3, 1, 5, 2, 1, 8]
def baseStart_3337911 : Nat := 118140960795 + 3337911 * 2 ^ 59
def prefixEnd_3337911 : Nat := 4983230072969 + 3 ^ 40 * 3337911 * 2
def baseEnd_3337911 : Nat := 126959461105910751226795

theorem tailTrace_3337911 : CollatzResearch.WordTrace tailWord_3337911 prefixEnd_3337911 126959461105910751226795 := by
  unfold tailWord_3337911
  simp only [CollatzResearch.WordTrace]
  refine ⟨121743615810325991658333587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81162410540217327772222391 121743615810325991658333587)
  ·
    refine ⟨182615423715488987487500381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121743615810325991658333587 182615423715488987487500381)
    ·
      refine ⟨68480783893308370307812643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182615423715488987487500381 68480783893308370307812643)
      ·
        refine ⟨102721175839962555461718965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68480783893308370307812643 102721175839962555461718965)
        ·
          refine ⟨9630110234996489574536153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102721175839962555461718965 9630110234996489574536153)
          ·
            refine ⟨7222582676247367180902115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9630110234996489574536153 7222582676247367180902115)
            ·
              refine ⟨10833874014371050771353173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222582676247367180902115 10833874014371050771353173)
              ·
                refine ⟨126959461105910751226795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10833874014371050771353173 126959461105910751226795)
                ·
                  rfl

theorem cell22_3337911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 8].length) (baseStart_3337911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337911 prefixEnd_3337911 := by exact prefixLift 3337911
  have htrace : WordTrace (prefixWord ++ tailWord_3337911) baseStart_3337911 baseEnd_3337911 := by
    simpa [prefixWord, tailWord_3337911, baseEnd_3337911] using wordTrace_append hprefix tailTrace_3337911
  have hstable : (prefixWord ++ tailWord_3337911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337911).length < 2 ^ (prefixWord ++ tailWord_3337911).sum := by decide
  have hdescent : baseEnd_3337911 < baseStart_3337911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337994 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_3337994 : Nat := 118140960795 + 3337994 * 2 ^ 59
def prefixEnd_3337994 : Nat := 4983230072969 + 3 ^ 40 * 3337994 * 2
def baseEnd_3337994 : Nat := 1142663562549412211215901

theorem tailTrace_3337994 : CollatzResearch.WordTrace tailWord_3337994 prefixEnd_3337994 1142663562549412211215901 := by
  unfold tailWord_3337994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30436660767256324208401259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81164428712683531222403357 30436660767256324208401259)
  ·
    refine ⟨45654991150884486312601889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30436660767256324208401259 45654991150884486312601889)
    ·
      refine ⟨34241243363163364734451417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45654991150884486312601889 34241243363163364734451417)
      ·
        refine ⟨25680932522372523550838563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34241243363163364734451417 25680932522372523550838563)
        ·
          refine ⟨38521398783558785326257845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25680932522372523550838563 38521398783558785326257845)
          ·
            refine ⟨3611381135958636124336673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38521398783558785326257845 3611381135958636124336673)
            ·
              refine ⟨2708535851968977093252505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611381135958636124336673 2708535851968977093252505)
              ·
                refine ⟨2031401888976732819939379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708535851968977093252505 2031401888976732819939379)
                ·
                  refine ⟨3047102833465099229909069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031401888976732819939379 3047102833465099229909069)
                  ·
                    refine ⟨1142663562549412211215901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3047102833465099229909069 1142663562549412211215901)
                    ·
                      rfl

theorem cell22_3337994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_3337994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3337994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3337994 prefixEnd_3337994 := by exact prefixLift 3337994
  have htrace : WordTrace (prefixWord ++ tailWord_3337994) baseStart_3337994 baseEnd_3337994 := by
    simpa [prefixWord, tailWord_3337994, baseEnd_3337994] using wordTrace_append hprefix tailTrace_3337994
  have hstable : (prefixWord ++ tailWord_3337994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337994).length < 2 ^ (prefixWord ++ tailWord_3337994).sum := by decide
  have hdescent : baseEnd_3337994 < baseStart_3337994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338001 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 6]
def baseStart_3338001 : Nat := 118140960795 + 3338001 * 2 ^ 59
def prefixEnd_3338001 : Nat := 4983230072969 + 3 ^ 40 * 3338001 * 2
def baseEnd_3338001 : Nat := 380888652930822175430293

theorem tailTrace_3338001 : CollatzResearch.WordTrace tailWord_3338001 prefixEnd_3338001 380888652930822175430293 := by
  unfold tailWord_3338001
  simp only [CollatzResearch.WordTrace]
  refine ⟨121746898379999937029109857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81164598919999958019406571 121746898379999937029109857)
  ·
    refine ⟨91310173784999952771832393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121746898379999937029109857 91310173784999952771832393)
    ·
      refine ⟨68482630338749964578874295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91310173784999952771832393 68482630338749964578874295)
      ·
        refine ⟨102723945508124946868311443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68482630338749964578874295 102723945508124946868311443)
        ·
          refine ⟨154085918262187420302467165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102723945508124946868311443 154085918262187420302467165)
          ·
            refine ⟨57782219348320282613425187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154085918262187420302467165 57782219348320282613425187)
            ·
              refine ⟨86673329022480423920137781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57782219348320282613425187 86673329022480423920137781)
              ·
                refine ⟨8125624595857539742512917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86673329022480423920137781 8125624595857539742512917)
                ·
                  refine ⟨380888652930822175430293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8125624595857539742512917 380888652930822175430293)
                  ·
                    rfl

theorem cell22_3338001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_3338001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338001 prefixEnd_3338001 := by exact prefixLift 3338001
  have htrace : WordTrace (prefixWord ++ tailWord_3338001) baseStart_3338001 baseEnd_3338001 := by
    simpa [prefixWord, tailWord_3338001, baseEnd_3338001] using wordTrace_append hprefix tailTrace_3338001
  have hstable : (prefixWord ++ tailWord_3338001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338001).length < 2 ^ (prefixWord ++ tailWord_3338001).sum := by decide
  have hdescent : baseEnd_3338001 < baseStart_3338001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338018 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3338018 : Nat := 118140960795 + 3338018 * 2 ^ 59
def prefixEnd_3338018 : Nat := 4983230072969 + 3 ^ 40 * 3338018 * 2
def baseEnd_3338018 : Nat := 380890592746628049538609

theorem tailTrace_3338018 : CollatzResearch.WordTrace tailWord_3338018 prefixEnd_3338018 380890592746628049538609 := by
  unfold tailWord_3338018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30436879605234587233119677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81165012280625565954985805 30436879605234587233119677)
  ·
    refine ⟨11413829851962970212419879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30436879605234587233119677 11413829851962970212419879)
    ·
      refine ⟨17120744777944455318629819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11413829851962970212419879 17120744777944455318629819)
      ·
        refine ⟨25681117166916682977944729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17120744777944455318629819 25681117166916682977944729)
        ·
          refine ⟨19260837875187512233458547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25681117166916682977944729 19260837875187512233458547)
          ·
            refine ⟨28891256812781268350187821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19260837875187512233458547 28891256812781268350187821)
            ·
              refine ⟨10834221304792975631320433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28891256812781268350187821 10834221304792975631320433)
              ·
                refine ⟨8125665978594731723490325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10834221304792975631320433 8125665978594731723490325)
                ·
                  refine ⟨380890592746628049538609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8125665978594731723490325 380890592746628049538609)
                  ·
                    rfl

theorem cell22_3338018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3338018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338018 prefixEnd_3338018 := by exact prefixLift 3338018
  have htrace : WordTrace (prefixWord ++ tailWord_3338018) baseStart_3338018 baseEnd_3338018 := by
    simpa [prefixWord, tailWord_3338018, baseEnd_3338018] using wordTrace_append hprefix tailTrace_3338018
  have hstable : (prefixWord ++ tailWord_3338018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338018).length < 2 ^ (prefixWord ++ tailWord_3338018).sum := by decide
  have hdescent : baseEnd_3338018 < baseStart_3338018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338031 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_3338031 : Nat := 118140960795 + 3338031 * 2 ^ 59
def prefixEnd_3338031 : Nat := 4983230072969 + 3 ^ 40 * 3338031 * 2
def baseEnd_3338031 : Nat := 1142676228405556448040787

theorem tailTrace_3338031 : CollatzResearch.WordTrace tailWord_3338031 prefixEnd_3338031 1142676228405556448040787 := by
  unfold tailWord_3338031
  simp only [CollatzResearch.WordTrace]
  refine ⟨121747992569891252152701947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81165328379927501435134631 121747992569891252152701947)
  ·
    refine ⟨182621988854836878229052921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121747992569891252152701947 182621988854836878229052921)
    ·
      refine ⟨136966491641127658671789691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182621988854836878229052921 136966491641127658671789691)
      ·
        refine ⟨205449737461691488007684537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136966491641127658671789691 205449737461691488007684537)
        ·
          refine ⟨154087303096268616005763403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205449737461691488007684537 154087303096268616005763403)
          ·
            refine ⟨231130954644402924008645105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154087303096268616005763403 231130954644402924008645105)
            ·
              refine ⟨173348215983302193006483829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231130954644402924008645105 173348215983302193006483829)
              ·
                refine ⟨16251395248434580594357859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173348215983302193006483829 16251395248434580594357859)
                ·
                  refine ⟨24377092872651870891536789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16251395248434580594357859 24377092872651870891536789)
                  ·
                    refine ⟨1142676228405556448040787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24377092872651870891536789 1142676228405556448040787)
                    ·
                      rfl

theorem cell22_3338031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_3338031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338031 prefixEnd_3338031 := by exact prefixLift 3338031
  have htrace : WordTrace (prefixWord ++ tailWord_3338031) baseStart_3338031 baseEnd_3338031 := by
    simpa [prefixWord, tailWord_3338031, baseEnd_3338031] using wordTrace_append hprefix tailTrace_3338031
  have hstable : (prefixWord ++ tailWord_3338031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338031).length < 2 ^ (prefixWord ++ tailWord_3338031).sum := by decide
  have hdescent : baseEnd_3338031 < baseStart_3338031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338033 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3338033 : Nat := 118140960795 + 3338033 * 2 ^ 59
def prefixEnd_3338033 : Nat := 4983230072969 + 3 ^ 40 * 3338033 * 2
def baseEnd_3338033 : Nat := 1142676913046429109490781

theorem tailTrace_3338033 : CollatzResearch.WordTrace tailWord_3338033 prefixEnd_3338033 1142676913046429109490781 := by
  unfold tailWord_3338033
  simp only [CollatzResearch.WordTrace]
  refine ⟨121748065515884006494274753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81165377010589337662849835 121748065515884006494274753)
  ·
    refine ⟨91311049136913004870706065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121748065515884006494274753 91311049136913004870706065)
    ·
      refine ⟨68483286852684753653029549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91311049136913004870706065 68483286852684753653029549)
      ·
        refine ⟨25681232569756782619886081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68483286852684753653029549 25681232569756782619886081)
        ·
          refine ⟨19260924427317586964914561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25681232569756782619886081 19260924427317586964914561)
          ·
            refine ⟨14445693320488190223685921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19260924427317586964914561 14445693320488190223685921)
            ·
              refine ⟨10834269990366142667764441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14445693320488190223685921 10834269990366142667764441)
              ·
                refine ⟨8125702492774607000823331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10834269990366142667764441 8125702492774607000823331)
                ·
                  refine ⟨12188553739161910501234997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8125702492774607000823331 12188553739161910501234997)
                  ·
                    refine ⟨1142676913046429109490781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12188553739161910501234997 1142676913046429109490781)
                    ·
                      rfl

theorem cell22_3338033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3338033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338033 prefixEnd_3338033 := by exact prefixLift 3338033
  have htrace : WordTrace (prefixWord ++ tailWord_3338033) baseStart_3338033 baseEnd_3338033 := by
    simpa [prefixWord, tailWord_3338033, baseEnd_3338033] using wordTrace_append hprefix tailTrace_3338033
  have hstable : (prefixWord ++ tailWord_3338033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338033).length < 2 ^ (prefixWord ++ tailWord_3338033).sum := by decide
  have hdescent : baseEnd_3338033 < baseStart_3338033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338080 : List Nat := [2, 1, 1, 3, 3, 4, 2, 6]
def baseStart_3338080 : Nat := 118140960795 + 3338080 * 2 ^ 59
def prefixEnd_3338080 : Nat := 4983230072969 + 3 ^ 40 * 3338080 * 2
def baseEnd_3338080 : Nat := 126965889122992961507293

theorem tailTrace_3338080 : CollatzResearch.WordTrace tailWord_3338080 prefixEnd_3338080 126965889122992961507293 := by
  unfold tailWord_3338080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60874889873356866760617847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81166519831142489014157129 60874889873356866760617847)
  ·
    refine ⟨91312334810035300140926771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60874889873356866760617847 91312334810035300140926771)
    ·
      refine ⟨136968502215052950211390157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91312334810035300140926771 136968502215052950211390157)
      ·
        refine ⟨51363188330644856329271309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136968502215052950211390157 51363188330644856329271309)
        ·
          refine ⟨19261195623991821123476741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51363188330644856329271309 19261195623991821123476741)
          ·
            refine ⟨3611474179498466460651889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19261195623991821123476741 3611474179498466460651889)
            ·
              refine ⟨2708605634623849845488917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611474179498466460651889 2708605634623849845488917)
              ·
                refine ⟨126965889122992961507293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2708605634623849845488917 126965889122992961507293)
                ·
                  rfl

theorem cell22_3338080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_3338080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338080 prefixEnd_3338080 := by exact prefixLift 3338080
  have htrace : WordTrace (prefixWord ++ tailWord_3338080) baseStart_3338080 baseEnd_3338080 := by
    simpa [prefixWord, tailWord_3338080, baseEnd_3338080] using wordTrace_append hprefix tailTrace_3338080
  have hstable : (prefixWord ++ tailWord_3338080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338080).length < 2 ^ (prefixWord ++ tailWord_3338080).sum := by decide
  have hdescent : baseEnd_3338080 < baseStart_3338080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338168 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_3338168 : Nat := 118140960795 + 3338168 * 2 ^ 59
def prefixEnd_3338168 : Nat := 4983230072969 + 3 ^ 40 * 3338168 * 2
def baseEnd_3338168 : Nat := 1142723126305333757365367

theorem tailTrace_3338168 : CollatzResearch.WordTrace tailWord_3338168 prefixEnd_3338168 1142723126305333757365367 := by
  unfold tailWord_3338168
  simp only [CollatzResearch.WordTrace]
  refine ⟨60876494685197462275219579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81168659580263283033626105 60876494685197462275219579)
  ·
    refine ⟨91314742027796193412829369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60876494685197462275219579 91314742027796193412829369)
    ·
      refine ⟨68486056520847145059622027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91314742027796193412829369 68486056520847145059622027)
      ·
        refine ⟨102729084781270717589433041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68486056520847145059622027 102729084781270717589433041)
        ·
          refine ⟨77046813585953038192074781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102729084781270717589433041 77046813585953038192074781)
          ·
            refine ⟨28892555094732389322028043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77046813585953038192074781 28892555094732389322028043)
            ·
              refine ⟨43338832642098583983042065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28892555094732389322028043 43338832642098583983042065)
              ·
                refine ⟨32504124481573937987281549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43338832642098583983042065 32504124481573937987281549)
                ·
                  refine ⟨12189046680590226745230581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32504124481573937987281549 12189046680590226745230581)
                  ·
                    refine ⟨1142723126305333757365367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12189046680590226745230581 1142723126305333757365367)
                    ·
                      rfl

theorem cell22_3338168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_3338168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338168 prefixEnd_3338168 := by exact prefixLift 3338168
  have htrace : WordTrace (prefixWord ++ tailWord_3338168) baseStart_3338168 baseEnd_3338168 := by
    simpa [prefixWord, tailWord_3338168, baseEnd_3338168] using wordTrace_append hprefix tailTrace_3338168
  have hstable : (prefixWord ++ tailWord_3338168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338168).length < 2 ^ (prefixWord ++ tailWord_3338168).sum := by decide
  have hdescent : baseEnd_3338168 < baseStart_3338168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338183 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3338183 : Nat := 118140960795 + 3338183 * 2 ^ 59
def prefixEnd_3338183 : Nat := 4983230072969 + 3 ^ 40 * 3338183 * 2
def baseEnd_3338183 : Nat := 1142728261111878718240321

theorem tailTrace_3338183 : CollatzResearch.WordTrace tailWord_3338183 prefixEnd_3338183 1142728261111878718240321 := by
  unfold tailWord_3338183
  simp only [CollatzResearch.WordTrace]
  refine ⟨121753536465340582112235203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81169024310227054741490135 121753536465340582112235203)
  ·
    refine ⟨182630304698010873168352805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121753536465340582112235203 182630304698010873168352805)
    ·
      refine ⟨34243182130877038719066151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182630304698010873168352805 34243182130877038719066151)
      ·
        refine ⟨51364773196315558078599227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34243182130877038719066151 51364773196315558078599227)
        ·
          refine ⟨77047159794473337117898841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51364773196315558078599227 77047159794473337117898841)
          ·
            refine ⟨57785369845855002838424131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77047159794473337117898841 57785369845855002838424131)
            ·
              refine ⟨86678054768782504257636197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57785369845855002838424131 86678054768782504257636197)
              ·
                refine ⟨16252135269146719548306787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86678054768782504257636197 16252135269146719548306787)
                ·
                  refine ⟨24378202903720079322460181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16252135269146719548306787 24378202903720079322460181)
                  ·
                    refine ⟨1142728261111878718240321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24378202903720079322460181 1142728261111878718240321)
                    ·
                      rfl

theorem cell22_3338183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3338183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338183 prefixEnd_3338183 := by exact prefixLift 3338183
  have htrace : WordTrace (prefixWord ++ tailWord_3338183) baseStart_3338183 baseEnd_3338183 := by
    simpa [prefixWord, tailWord_3338183, baseEnd_3338183] using wordTrace_append hprefix tailTrace_3338183
  have hstable : (prefixWord ++ tailWord_3338183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338183).length < 2 ^ (prefixWord ++ tailWord_3338183).sum := by decide
  have hdescent : baseEnd_3338183 < baseStart_3338183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338215 : List Nat := [1, 1, 5, 2, 3, 1, 9]
def baseStart_3338215 : Nat := 118140960795 + 3338215 * 2 ^ 59
def prefixEnd_3338215 : Nat := 4983230072969 + 3 ^ 40 * 3338215 * 2
def baseEnd_3338215 : Nat := 42323674643179307460749

theorem tailTrace_3338215 : CollatzResearch.WordTrace tailWord_3338215 prefixEnd_3338215 42323674643179307460749 := by
  unfold tailWord_3338215
  simp only [CollatzResearch.WordTrace]
  refine ⟨121754703601224651577400099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81169802400816434384933399 121754703601224651577400099)
  ·
    refine ⟨182632055401836977366100149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121754703601224651577400099 182632055401836977366100149)
    ·
      refine ⟨17121755193922216628071889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182632055401836977366100149 17121755193922216628071889)
      ·
        refine ⟨12841316395441662471053917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17121755193922216628071889 12841316395441662471053917)
        ·
          refine ⟨4815493648290623426645219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12841316395441662471053917 4815493648290623426645219)
          ·
            refine ⟨7223240472435935139967829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815493648290623426645219 7223240472435935139967829)
            ·
              refine ⟨42323674643179307460749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7223240472435935139967829 42323674643179307460749)
              ·
                rfl

theorem cell22_3338215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 9].length) (baseStart_3338215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338215 prefixEnd_3338215 := by exact prefixLift 3338215
  have htrace : WordTrace (prefixWord ++ tailWord_3338215) baseStart_3338215 baseEnd_3338215 := by
    simpa [prefixWord, tailWord_3338215, baseEnd_3338215] using wordTrace_append hprefix tailTrace_3338215
  have hstable : (prefixWord ++ tailWord_3338215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338215).length < 2 ^ (prefixWord ++ tailWord_3338215).sum := by decide
  have hdescent : baseEnd_3338215 < baseStart_3338215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338247 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 3, 3]
def baseStart_3338247 : Nat := 118140960795 + 3338247 * 2 ^ 59
def prefixEnd_3338247 : Nat := 4983230072969 + 3 ^ 40 * 3338247 * 2
def baseEnd_3338247 : Nat := 1142750169619803884640125

theorem tailTrace_3338247 : CollatzResearch.WordTrace tailWord_3338247 prefixEnd_3338247 1142750169619803884640125 := by
  unfold tailWord_3338247
  simp only [CollatzResearch.WordTrace]
  refine ⟨121755870737108721042564995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81170580491405814028376663 121755870737108721042564995)
  ·
    refine ⟨182633806105663081563847493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121755870737108721042564995 182633806105663081563847493)
    ·
      refine ⟨34243838644811827793221405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182633806105663081563847493 34243838644811827793221405)
      ·
        refine ⟨12841439491804435422458027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34243838644811827793221405 12841439491804435422458027)
        ·
          refine ⟨19262159237706653133687041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12841439491804435422458027 19262159237706653133687041)
          ·
            refine ⟨14446619428279989850265281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19262159237706653133687041 14446619428279989850265281)
            ·
              refine ⟨10834964571209992387698961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14446619428279989850265281 10834964571209992387698961)
              ·
                refine ⟨8126223428407494290774221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10834964571209992387698961 8126223428407494290774221)
                ·
                  refine ⟨3047333785652810359040333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8126223428407494290774221 3047333785652810359040333)
                  ·
                    refine ⟨1142750169619803884640125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3047333785652810359040333 1142750169619803884640125)
                    ·
                      rfl

theorem cell22_3338247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_3338247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338247 prefixEnd_3338247 := by exact prefixLift 3338247
  have htrace : WordTrace (prefixWord ++ tailWord_3338247) baseStart_3338247 baseEnd_3338247 := by
    simpa [prefixWord, tailWord_3338247, baseEnd_3338247] using wordTrace_append hprefix tailTrace_3338247
  have hstable : (prefixWord ++ tailWord_3338247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338247).length < 2 ^ (prefixWord ++ tailWord_3338247).sum := by decide
  have hdescent : baseEnd_3338247 < baseStart_3338247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338335 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 4, 4]
def baseStart_3338335 : Nat := 118140960795 + 3338335 * 2 ^ 59
def prefixEnd_3338335 : Nat := 4983230072969 + 3 ^ 40 * 3338335 * 2
def baseEnd_3338335 : Nat := 1142780293818200988439855

theorem tailTrace_3338335 : CollatzResearch.WordTrace tailWord_3338335 prefixEnd_3338335 1142780293818200988439855 := by
  unfold tailWord_3338335
  simp only [CollatzResearch.WordTrace]
  refine ⟨121759080360789912071768459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81172720240526608047845639 121759080360789912071768459)
  ·
    refine ⟨182638620541184868107652689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121759080360789912071768459 182638620541184868107652689)
    ·
      refine ⟨136978965405888651080739517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182638620541184868107652689 136978965405888651080739517)
      ·
        refine ⟨51367112027208244155277319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136978965405888651080739517 51367112027208244155277319)
        ·
          refine ⟨77050668040812366232915979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51367112027208244155277319 77050668040812366232915979)
          ·
            refine ⟨115576002061218549349373969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77050668040812366232915979 115576002061218549349373969)
            ·
              refine ⟨86682001545913912012030477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115576002061218549349373969 86682001545913912012030477)
              ·
                refine ⟨32505750579717717004511429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86682001545913912012030477 32505750579717717004511429)
                ·
                  refine ⟨6094828233697071938345893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32505750579717717004511429 6094828233697071938345893)
                  ·
                    refine ⟨1142780293818200988439855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094828233697071938345893 1142780293818200988439855)
                    ·
                      rfl

theorem cell22_3338335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_3338335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338335 prefixEnd_3338335 := by exact prefixLift 3338335
  have htrace : WordTrace (prefixWord ++ tailWord_3338335) baseStart_3338335 baseEnd_3338335 := by
    simpa [prefixWord, tailWord_3338335, baseEnd_3338335] using wordTrace_append hprefix tailTrace_3338335
  have hstable : (prefixWord ++ tailWord_3338335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338335).length < 2 ^ (prefixWord ++ tailWord_3338335).sum := by decide
  have hdescent : baseEnd_3338335 < baseStart_3338335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338339 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 4]
def baseStart_3338339 : Nat := 118140960795 + 3338339 * 2 ^ 59
def prefixEnd_3338339 : Nat := 4983230072969 + 3 ^ 40 * 3338339 * 2
def baseEnd_3338339 : Nat := 380927221033315437113281

theorem tailTrace_3338339 : CollatzResearch.WordTrace tailWord_3338339 prefixEnd_3338339 380927221033315437113281 := by
  unfold tailWord_3338339
  simp only [CollatzResearch.WordTrace]
  refine ⟨121759226252775420754914071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81172817501850280503276047 121759226252775420754914071)
  ·
    refine ⟨182638839379163131132371107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121759226252775420754914071 182638839379163131132371107)
    ·
      refine ⟨273958259068744696698556661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182638839379163131132371107 273958259068744696698556661)
      ·
        refine ⟨25683586787694815315489687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273958259068744696698556661 25683586787694815315489687)
        ·
          refine ⟨38525380181542222973234531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25683586787694815315489687 38525380181542222973234531)
          ·
            refine ⟨57788070272313334459851797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38525380181542222973234531 57788070272313334459851797)
            ·
              refine ⟨2708815794014687552805553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57788070272313334459851797 2708815794014687552805553)
              ·
                refine ⟨2031611845511015664604165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708815794014687552805553 2031611845511015664604165)
                ·
                  refine ⟨380927221033315437113281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031611845511015664604165 380927221033315437113281)
                  ·
                    rfl

theorem cell22_3338339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 4].length) (baseStart_3338339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338339 prefixEnd_3338339 := by exact prefixLift 3338339
  have htrace : WordTrace (prefixWord ++ tailWord_3338339) baseStart_3338339 baseEnd_3338339 := by
    simpa [prefixWord, tailWord_3338339, baseEnd_3338339] using wordTrace_append hprefix tailTrace_3338339
  have hstable : (prefixWord ++ tailWord_3338339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338339).length < 2 ^ (prefixWord ++ tailWord_3338339).sum := by decide
  have hdescent : baseEnd_3338339 < baseStart_3338339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338354 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_3338354 : Nat := 118140960795 + 3338354 * 2 ^ 59
def prefixEnd_3338354 : Nat := 4983230072969 + 3 ^ 40 * 3338354 * 2
def baseEnd_3338354 : Nat := 1142786797906491272214797

theorem tailTrace_3338354 : CollatzResearch.WordTrace tailWord_3338354 prefixEnd_3338354 1142786797906491272214797 := by
  unfold tailWord_3338354
  simp only [CollatzResearch.WordTrace]
  refine ⟨30439943336930269579177529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81173182231814052211140077 30439943336930269579177529)
  ·
    refine ⟨22829957502697702184383147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30439943336930269579177529 22829957502697702184383147)
    ·
      refine ⟨34244936254046553276574721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829957502697702184383147 34244936254046553276574721)
      ·
        refine ⟨25683702190534914957431041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34244936254046553276574721 25683702190534914957431041)
        ·
          refine ⟨19262776642901186218073281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25683702190534914957431041 19262776642901186218073281)
          ·
            refine ⟨14447082482175889663554961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19262776642901186218073281 14447082482175889663554961)
            ·
              refine ⟨10835311861631917247666221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14447082482175889663554961 10835311861631917247666221)
              ·
                refine ⟨4063241948111968967874833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10835311861631917247666221 4063241948111968967874833)
                ·
                  refine ⟨3047431461083976725906125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4063241948111968967874833 3047431461083976725906125)
                  ·
                    refine ⟨1142786797906491272214797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3047431461083976725906125 1142786797906491272214797)
                    ·
                      rfl

theorem cell22_3338354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_3338354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338354 prefixEnd_3338354 := by exact prefixLift 3338354
  have htrace : WordTrace (prefixWord ++ tailWord_3338354) baseStart_3338354 baseEnd_3338354 := by
    simpa [prefixWord, tailWord_3338354, baseEnd_3338354] using wordTrace_append hprefix tailTrace_3338354
  have hstable : (prefixWord ++ tailWord_3338354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338354).length < 2 ^ (prefixWord ++ tailWord_3338354).sum := by decide
  have hdescent : baseEnd_3338354 < baseStart_3338354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338390 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3338390 : Nat := 118140960795 + 3338390 * 2 ^ 59
def prefixEnd_3338390 : Nat := 4983230072969 + 3 ^ 40 * 3338390 * 2
def baseEnd_3338390 : Nat := 380933040480733059438229

theorem tailTrace_3338390 : CollatzResearch.WordTrace tailWord_3338390 prefixEnd_3338390 380933040480733059438229 := by
  unfold tailWord_3338390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7610067898474416029063789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81174057583727104310013749 7610067898474416029063789)
  ·
    refine ⟨2853775461927906010898921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7610067898474416029063789 2853775461927906010898921)
    ·
      refine ⟨2140331596445929508174191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2853775461927906010898921 2140331596445929508174191)
      ·
        refine ⟨3210497394668894262261287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140331596445929508174191 3210497394668894262261287)
        ·
          refine ⟨4815746092003341393391931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210497394668894262261287 4815746092003341393391931)
          ·
            refine ⟨7223619138005012090087897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815746092003341393391931 7223619138005012090087897)
            ·
              refine ⟨5417714353503759067565923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223619138005012090087897 5417714353503759067565923)
              ·
                refine ⟨8126571530255638601348885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417714353503759067565923 8126571530255638601348885)
                ·
                  refine ⟨380933040480733059438229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8126571530255638601348885 380933040480733059438229)
                  ·
                    rfl

theorem cell22_3338390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3338390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338390 prefixEnd_3338390 := by exact prefixLift 3338390
  have htrace : WordTrace (prefixWord ++ tailWord_3338390) baseStart_3338390 baseEnd_3338390 := by
    simpa [prefixWord, tailWord_3338390, baseEnd_3338390] using wordTrace_append hprefix tailTrace_3338390
  have hstable : (prefixWord ++ tailWord_3338390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338390).length < 2 ^ (prefixWord ++ tailWord_3338390).sum := by decide
  have hdescent : baseEnd_3338390 < baseStart_3338390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338399 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 3, 3]
def baseStart_3338399 : Nat := 118140960795 + 3338399 * 2 ^ 59
def prefixEnd_3338399 : Nat := 4983230072969 + 3 ^ 40 * 3338399 * 2
def baseEnd_3338399 : Nat := 1142802202326126154839659

theorem tailTrace_3338399 : CollatzResearch.WordTrace tailWord_3338399 prefixEnd_3338399 1142802202326126154839659 := by
  unfold tailWord_3338399
  simp only [CollatzResearch.WordTrace]
  refine ⟨121761414632558051002098251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81174276421705367334732167 121761414632558051002098251)
  ·
    refine ⟨182642121948837076503147377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121761414632558051002098251 182642121948837076503147377)
    ·
      refine ⟨136981591461627807377360533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182642121948837076503147377 136981591461627807377360533)
      ·
        refine ⟨6421012099763803470813775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136981591461627807377360533 6421012099763803470813775)
        ·
          refine ⟨9631518149645705206220663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6421012099763803470813775 9631518149645705206220663)
          ·
            refine ⟨14447277224468557809330995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631518149645705206220663 14447277224468557809330995)
            ·
              refine ⟨21670915836702836713996493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14447277224468557809330995 21670915836702836713996493)
              ·
                refine ⟨8126593438763563767748685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21670915836702836713996493 8126593438763563767748685)
                ·
                  refine ⟨3047472539536336412905757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8126593438763563767748685 3047472539536336412905757)
                  ·
                    refine ⟨1142802202326126154839659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3047472539536336412905757 1142802202326126154839659)
                    ·
                      rfl

theorem cell22_3338399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_3338399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338399 prefixEnd_3338399 := by exact prefixLift 3338399
  have htrace : WordTrace (prefixWord ++ tailWord_3338399) baseStart_3338399 baseEnd_3338399 := by
    simpa [prefixWord, tailWord_3338399, baseEnd_3338399] using wordTrace_append hprefix tailTrace_3338399
  have hstable : (prefixWord ++ tailWord_3338399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338399).length < 2 ^ (prefixWord ++ tailWord_3338399).sum := by decide
  have hdescent : baseEnd_3338399 < baseStart_3338399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338457 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 6]
def baseStart_3338457 : Nat := 118140960795 + 3338457 * 2 ^ 59
def prefixEnd_3338457 : Nat := 4983230072969 + 3 ^ 40 * 3338457 * 2
def baseEnd_3338457 : Nat := 380940685637144445629827

theorem tailTrace_3338457 : CollatzResearch.WordTrace tailWord_3338457 prefixEnd_3338457 380940685637144445629827 := by
  unfold tailWord_3338457
  simp only [CollatzResearch.WordTrace]
  refine ⟨121763530066347926907709625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81175686710898617938473083 121763530066347926907709625)
  ·
    refine ⟨91322647549760945180782219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121763530066347926907709625 91322647549760945180782219)
    ·
      refine ⟨136983971324641417771173329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91322647549760945180782219 136983971324641417771173329)
      ·
        refine ⟨102737978493481063328379997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136983971324641417771173329 102737978493481063328379997)
        ·
          refine ⟨38526741935055398748142499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102737978493481063328379997 38526741935055398748142499)
          ·
            refine ⟨57790112902583098122213749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38526741935055398748142499 57790112902583098122213749)
            ·
              refine ⟨5417823084617165448957539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57790112902583098122213749 5417823084617165448957539)
              ·
                refine ⟨8126734626925748173436309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417823084617165448957539 8126734626925748173436309)
                ·
                  refine ⟨380940685637144445629827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8126734626925748173436309 380940685637144445629827)
                  ·
                    rfl

theorem cell22_3338457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_3338457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338457 prefixEnd_3338457 := by exact prefixLift 3338457
  have htrace : WordTrace (prefixWord ++ tailWord_3338457) baseStart_3338457 baseEnd_3338457 := by
    simpa [prefixWord, tailWord_3338457, baseEnd_3338457] using wordTrace_append hprefix tailTrace_3338457
  have hstable : (prefixWord ++ tailWord_3338457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338457).length < 2 ^ (prefixWord ++ tailWord_3338457).sum := by decide
  have hdescent : baseEnd_3338457 < baseStart_3338457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338504 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3338504 : Nat := 118140960795 + 3338504 * 2 ^ 59
def prefixEnd_3338504 : Nat := 4983230072969 + 3 ^ 40 * 3338504 * 2
def baseEnd_3338504 : Nat := 1142838145971940880964337

theorem tailTrace_3338504 : CollatzResearch.WordTrace tailWord_3338504 prefixEnd_3338504 1142838145971940880964337 := by
  unfold tailWord_3338504
  simp only [CollatzResearch.WordTrace]
  refine ⟨60882622148588826967335283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81176829531451769289780377 60882622148588826967335283)
  ·
    refine ⟨91323933222883240451002925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60882622148588826967335283 91323933222883240451002925)
    ·
      refine ⟨34246474958581215169126097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91323933222883240451002925 34246474958581215169126097)
      ·
        refine ⟨25684856218935911376844573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34246474958581215169126097 25684856218935911376844573)
        ·
          refine ⟨9631821082100966766316715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25684856218935911376844573 9631821082100966766316715)
          ·
            refine ⟨14447731623151450149475073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631821082100966766316715 14447731623151450149475073)
            ·
              refine ⟨10835798717363587612106305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14447731623151450149475073 10835798717363587612106305)
              ·
                refine ⟨8126849038022690709079729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10835798717363587612106305 8126849038022690709079729)
                ·
                  refine ⟨6095136778517018031809797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126849038022690709079729 6095136778517018031809797)
                  ·
                    refine ⟨1142838145971940880964337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095136778517018031809797 1142838145971940880964337)
                    ·
                      rfl

theorem cell22_3338504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3338504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338504 prefixEnd_3338504 := by exact prefixLift 3338504
  have htrace : WordTrace (prefixWord ++ tailWord_3338504) baseStart_3338504 baseEnd_3338504 := by
    simpa [prefixWord, tailWord_3338504, baseEnd_3338504] using wordTrace_append hprefix tailTrace_3338504
  have hstable : (prefixWord ++ tailWord_3338504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338504).length < 2 ^ (prefixWord ++ tailWord_3338504).sum := by decide
  have hdescent : baseEnd_3338504 < baseStart_3338504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338519 : List Nat := [1, 1, 3, 4, 1, 4, 1, 7]
def baseStart_3338519 : Nat := 118140960795 + 3338519 * 2 ^ 59
def prefixEnd_3338519 : Nat := 4983230072969 + 3 ^ 40 * 3338519 * 2
def baseEnd_3338519 : Nat := 126982586753165093537699

theorem tailTrace_3338519 : CollatzResearch.WordTrace tailWord_3338519 prefixEnd_3338519 126982586753165093537699 := by
  unfold tailWord_3338519
  simp only [CollatzResearch.WordTrace]
  refine ⟨121765791392123311496466611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81177194261415540997644407 121765791392123311496466611)
  ·
    refine ⟨182648687088184967244699917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121765791392123311496466611 182648687088184967244699917)
    ·
      refine ⟨68493257658069362716762469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182648687088184967244699917 68493257658069362716762469)
      ·
        refine ⟨12842485810888005509392963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68493257658069362716762469 12842485810888005509392963)
        ·
          refine ⟨19263728716332008264089445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12842485810888005509392963 19263728716332008264089445)
          ·
            refine ⟨3611949134312251549516771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19263728716332008264089445 3611949134312251549516771)
            ·
              refine ⟨5417923701468377324275157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611949134312251549516771 5417923701468377324275157)
              ·
                refine ⟨126982586753165093537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5417923701468377324275157 126982586753165093537699)
                ·
                  rfl

theorem cell22_3338519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 7].length) (baseStart_3338519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338519 prefixEnd_3338519 := by exact prefixLift 3338519
  have htrace : WordTrace (prefixWord ++ tailWord_3338519) baseStart_3338519 baseEnd_3338519 := by
    simpa [prefixWord, tailWord_3338519, baseEnd_3338519] using wordTrace_append hprefix tailTrace_3338519
  have hstable : (prefixWord ++ tailWord_3338519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338519).length < 2 ^ (prefixWord ++ tailWord_3338519).sum := by decide
  have hdescent : baseEnd_3338519 < baseStart_3338519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338536 : List Nat := [2, 1, 5, 1, 3, 1, 3, 6]
def baseStart_3338536 : Nat := 118140960795 + 3338536 * 2 ^ 59
def prefixEnd_3338536 : Nat := 4983230072969 + 3 ^ 40 * 3338536 * 2
def baseEnd_3338536 : Nat := 126983233358433718240471

theorem tailTrace_3338536 : CollatzResearch.WordTrace tailWord_3338536 prefixEnd_3338536 126983233358433718240471 := by
  unfold tailWord_3338536
  simp only [CollatzResearch.WordTrace]
  refine ⟨60883205716530861699917731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81177607622041148933223641 60883205716530861699917731)
  ·
    refine ⟨91324808574796292549876597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60883205716530861699917731 91324808574796292549876597)
    ·
      refine ⟨8561700803887152426550931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91324808574796292549876597 8561700803887152426550931)
      ·
        refine ⟨12842551205830728639826397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8561700803887152426550931 12842551205830728639826397)
        ·
          refine ⟨4815956702186523239934899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12842551205830728639826397 4815956702186523239934899)
          ·
            refine ⟨7223935053279784859902349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815956702186523239934899 7223935053279784859902349)
            ·
              refine ⟨2708975644979919322463381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7223935053279784859902349 2708975644979919322463381)
              ·
                refine ⟨126983233358433718240471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2708975644979919322463381 126983233358433718240471)
                ·
                  rfl

theorem cell22_3338536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_3338536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338536 prefixEnd_3338536 := by exact prefixLift 3338536
  have htrace : WordTrace (prefixWord ++ tailWord_3338536) baseStart_3338536 baseEnd_3338536 := by
    simpa [prefixWord, tailWord_3338536, baseEnd_3338536] using wordTrace_append hprefix tailTrace_3338536
  have hstable : (prefixWord ++ tailWord_3338536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338536).length < 2 ^ (prefixWord ++ tailWord_3338536).sum := by decide
  have hdescent : baseEnd_3338536 < baseStart_3338536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338538 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3338538 : Nat := 118140960795 + 3338538 * 2 ^ 59
def prefixEnd_3338538 : Nat := 4983230072969 + 3 ^ 40 * 3338538 * 2
def baseEnd_3338538 : Nat := 1142849784866776125614233

theorem tailTrace_3338538 : CollatzResearch.WordTrace tailWord_3338538 prefixEnd_3338538 1142849784866776125614233 := by
  unfold tailWord_3338538
  simp only [CollatzResearch.WordTrace]
  refine ⟨30441621094763619435352067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81177656252702985160938845 30441621094763619435352067)
  ·
    refine ⟨45662431642145429153028101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30441621094763619435352067 45662431642145429153028101)
    ·
      refine ⟨8561705932902267966192769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45662431642145429153028101 8561705932902267966192769)
      ·
        refine ⟨6421279449676700974644577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8561705932902267966192769 6421279449676700974644577)
        ·
          refine ⟨4815959587257525730983433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6421279449676700974644577 4815959587257525730983433)
          ·
            refine ⟨3611969690443144298237575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4815959587257525730983433 3611969690443144298237575)
            ·
              refine ⟨5417954535664716447356363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611969690443144298237575 5417954535664716447356363)
              ·
                refine ⟨8126931803497074671034545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417954535664716447356363 8126931803497074671034545)
                ·
                  refine ⟨6095198852622806003275909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126931803497074671034545 6095198852622806003275909)
                  ·
                    refine ⟨1142849784866776125614233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095198852622806003275909 1142849784866776125614233)
                    ·
                      rfl

theorem cell22_3338538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3338538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338538 prefixEnd_3338538 := by exact prefixLift 3338538
  have htrace : WordTrace (prefixWord ++ tailWord_3338538) baseStart_3338538 baseEnd_3338538 := by
    simpa [prefixWord, tailWord_3338538, baseEnd_3338538] using wordTrace_append hprefix tailTrace_3338538
  have hstable : (prefixWord ++ tailWord_3338538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338538).length < 2 ^ (prefixWord ++ tailWord_3338538).sum := by decide
  have hdescent : baseEnd_3338538 < baseStart_3338538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338547 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 7]
def baseStart_3338547 : Nat := 118140960795 + 3338547 * 2 ^ 59
def prefixEnd_3338547 : Nat := 4983230072969 + 3 ^ 40 * 3338547 * 2
def baseEnd_3338547 : Nat := 380950955250234367379735

theorem tailTrace_3338547 : CollatzResearch.WordTrace tailWord_3338547 prefixEnd_3338547 380950955250234367379735 := by
  unfold tailWord_3338547
  simp only [CollatzResearch.WordTrace]
  refine ⟨121766812636021872278485895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81177875090681248185657263 121766812636021872278485895)
  ·
    refine ⟨182650218954032808417728843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121766812636021872278485895 182650218954032808417728843)
    ·
      refine ⟨273975328431049212626593265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182650218954032808417728843 273975328431049212626593265)
      ·
        refine ⟨205481496323286909469944949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273975328431049212626593265 205481496323286909469944949)
        ·
          refine ⟨19263890280308147762807339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205481496323286909469944949 19263890280308147762807339)
          ·
            refine ⟨28895835420462221644211009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19263890280308147762807339 28895835420462221644211009)
            ·
              refine ⟨21671876565346666233158257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28895835420462221644211009 21671876565346666233158257)
              ·
                refine ⟨16253907424009999674868693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21671876565346666233158257 16253907424009999674868693)
                ·
                  refine ⟨380950955250234367379735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16253907424009999674868693 380950955250234367379735)
                  ·
                    rfl

theorem cell22_3338547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_3338547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338547 prefixEnd_3338547 := by exact prefixLift 3338547
  have htrace : WordTrace (prefixWord ++ tailWord_3338547) baseStart_3338547 baseEnd_3338547 := by
    simpa [prefixWord, tailWord_3338547, baseEnd_3338547] using wordTrace_append hprefix tailTrace_3338547
  have hstable : (prefixWord ++ tailWord_3338547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338547).length < 2 ^ (prefixWord ++ tailWord_3338547).sum := by decide
  have hdescent : baseEnd_3338547 < baseStart_3338547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338656 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_3338656 : Nat := 118140960795 + 3338656 * 2 ^ 59
def prefixEnd_3338656 : Nat := 4983230072969 + 3 ^ 40 * 3338656 * 2
def baseEnd_3338656 : Nat := 1142890178678263151163871

theorem tailTrace_3338656 : CollatzResearch.WordTrace tailWord_3338656 prefixEnd_3338656 1142890178678263151163871 := by
  unfold tailWord_3338656
  simp only [CollatzResearch.WordTrace]
  refine ⟨60885394096313491947101911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81180525461751322596135881 60885394096313491947101911)
  ·
    refine ⟨91328091144470237920652867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60885394096313491947101911 91328091144470237920652867)
    ·
      refine ⟨136992136716705356880979301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91328091144470237920652867 136992136716705356880979301)
      ·
        refine ⟨25686025634382254415183619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136992136716705356880979301 25686025634382254415183619)
        ·
          refine ⟨38529038451573381622775429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25686025634382254415183619 38529038451573381622775429)
          ·
            refine ⟨7224194709670009054270393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38529038451573381622775429 7224194709670009054270393)
            ·
              refine ⟨5418146032252506790702795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7224194709670009054270393 5418146032252506790702795)
              ·
                refine ⟨8127219048378760186054193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5418146032252506790702795 8127219048378760186054193)
                ·
                  refine ⟨6095414286284070139540645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8127219048378760186054193 6095414286284070139540645)
                  ·
                    refine ⟨1142890178678263151163871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095414286284070139540645 1142890178678263151163871)
                    ·
                      rfl

theorem cell22_3338656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_3338656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338656 prefixEnd_3338656 := by exact prefixLift 3338656
  have htrace : WordTrace (prefixWord ++ tailWord_3338656) baseStart_3338656 baseEnd_3338656 := by
    simpa [prefixWord, tailWord_3338656, baseEnd_3338656] using wordTrace_append hprefix tailTrace_3338656
  have hstable : (prefixWord ++ tailWord_3338656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338656).length < 2 ^ (prefixWord ++ tailWord_3338656).sum := by decide
  have hdescent : baseEnd_3338656 < baseStart_3338656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338677 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 4]
def baseStart_3338677 : Nat := 118140960795 + 3338677 * 2 ^ 59
def prefixEnd_3338677 : Nat := 4983230072969 + 3 ^ 40 * 3338677 * 2
def baseEnd_3338677 : Nat := 380965789135808698796269

theorem tailTrace_3338677 : CollatzResearch.WordTrace tailWord_3338677 prefixEnd_3338677 380965789135808698796269 := by
  unfold tailWord_3338677
  simp only [CollatzResearch.WordTrace]
  refine ⟨121771554125550904480718285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81181036083700602987145523 121771554125550904480718285)
  ·
    refine ⟨45664332797081589180269357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121771554125550904480718285 45664332797081589180269357)
    ·
      refine ⟨17124124798905595942601009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45664332797081589180269357 17124124798905595942601009)
      ·
        refine ⟨12843093599179196956950757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17124124798905595942601009 12843093599179196956950757)
        ·
          refine ⟨2408080049846099429428267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12843093599179196956950757 2408080049846099429428267)
          ·
            refine ⟨3612120074769149144142401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408080049846099429428267 3612120074769149144142401)
            ·
              refine ⟨2709090056076861858106801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612120074769149144142401 2709090056076861858106801)
              ·
                refine ⟨2031817542057646393580101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2709090056076861858106801 2031817542057646393580101)
                ·
                  refine ⟨380965789135808698796269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031817542057646393580101 380965789135808698796269)
                  ·
                    rfl

theorem cell22_3338677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_3338677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338677 prefixEnd_3338677 := by exact prefixLift 3338677
  have htrace : WordTrace (prefixWord ++ tailWord_3338677) baseStart_3338677 baseEnd_3338677 := by
    simpa [prefixWord, tailWord_3338677, baseEnd_3338677] using wordTrace_append hprefix tailTrace_3338677
  have hstable : (prefixWord ++ tailWord_3338677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338677).length < 2 ^ (prefixWord ++ tailWord_3338677).sum := by decide
  have hdescent : baseEnd_3338677 < baseStart_3338677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338714 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_3338714 : Nat := 118140960795 + 3338714 * 2 ^ 59
def prefixEnd_3338714 : Nat := 4983230072969 + 3 ^ 40 * 3338714 * 2
def baseEnd_3338714 : Nat := 1142910033263570333213693

theorem tailTrace_3338714 : CollatzResearch.WordTrace tailWord_3338714 prefixEnd_3338714 1142910033263570333213693 := by
  unfold tailWord_3338714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443225906604214949953799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81181935750944573199876797 30443225906604214949953799)
  ·
    refine ⟨45664838859906322424930699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30443225906604214949953799 45664838859906322424930699)
    ·
      refine ⟨68497258289859483637396049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45664838859906322424930699 68497258289859483637396049)
      ·
        refine ⟨51372943717394612728047037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68497258289859483637396049 51372943717394612728047037)
        ·
          refine ⟨19264853894022979773017639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51372943717394612728047037 19264853894022979773017639)
          ·
            refine ⟨28897280841034469659526459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19264853894022979773017639 28897280841034469659526459)
            ·
              refine ⟨43345921261551704489289689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28897280841034469659526459 43345921261551704489289689)
              ·
                refine ⟨32509440946163778366967267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43345921261551704489289689 32509440946163778366967267)
                ·
                  refine ⟨48764161419245667550450901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32509440946163778366967267 48764161419245667550450901)
                  ·
                    refine ⟨1142910033263570333213693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48764161419245667550450901 1142910033263570333213693)
                    ·
                      rfl

theorem cell22_3338714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_3338714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338714 prefixEnd_3338714 := by exact prefixLift 3338714
  have htrace : WordTrace (prefixWord ++ tailWord_3338714) baseStart_3338714 baseEnd_3338714 := by
    simpa [prefixWord, tailWord_3338714, baseEnd_3338714] using wordTrace_append hprefix tailTrace_3338714
  have hstable : (prefixWord ++ tailWord_3338714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338714).length < 2 ^ (prefixWord ++ tailWord_3338714).sum := by decide
  have hdescent : baseEnd_3338714 < baseStart_3338714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338729 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_3338729 : Nat := 118140960795 + 3338729 * 2 ^ 59
def prefixEnd_3338729 : Nat := 4983230072969 + 3 ^ 40 * 3338729 * 2
def baseEnd_3338729 : Nat := 1142915168070115294088647

theorem tailTrace_3338729 : CollatzResearch.WordTrace tailWord_3338729 prefixEnd_3338729 1142915168070115294088647 := by
  unfold tailWord_3338729
  simp only [CollatzResearch.WordTrace]
  refine ⟨121773450721362517361611241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81182300480908344907740827 121773450721362517361611241)
  ·
    refine ⟨91330088041021888021208431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121773450721362517361611241 91330088041021888021208431)
    ·
      refine ⟨136995132061532832031812647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91330088041021888021208431 136995132061532832031812647)
      ·
        refine ⟨205492698092299248047718971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136995132061532832031812647 205492698092299248047718971)
        ·
          refine ⟨308239047138448872071578457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205492698092299248047718971 308239047138448872071578457)
          ·
            refine ⟨231179285353836654053683843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308239047138448872071578457 231179285353836654053683843)
            ·
              refine ⟨346768928030754981080525765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231179285353836654053683843 346768928030754981080525765)
              ·
                refine ⟨65019174005766558952598581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346768928030754981080525765 65019174005766558952598581)
                ·
                  refine ⟨6095547563040614901806117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65019174005766558952598581 6095547563040614901806117)
                  ·
                    refine ⟨1142915168070115294088647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095547563040614901806117 1142915168070115294088647)
                    ·
                      rfl

theorem cell22_3338729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_3338729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338729 prefixEnd_3338729 := by exact prefixLift 3338729
  have htrace : WordTrace (prefixWord ++ tailWord_3338729) baseStart_3338729 baseEnd_3338729 := by
    simpa [prefixWord, tailWord_3338729, baseEnd_3338729] using wordTrace_append hprefix tailTrace_3338729
  have hstable : (prefixWord ++ tailWord_3338729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338729).length < 2 ^ (prefixWord ++ tailWord_3338729).sum := by decide
  have hdescent : baseEnd_3338729 < baseStart_3338729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338733 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3338733 : Nat := 118140960795 + 3338733 * 2 ^ 59
def prefixEnd_3338733 : Nat := 4983230072969 + 3 ^ 40 * 3338733 * 2
def baseEnd_3338733 : Nat := 380972179117286872329545

theorem tailTrace_3338733 : CollatzResearch.WordTrace tailWord_3338733 prefixEnd_3338733 380972179117286872329545 := by
  unfold tailWord_3338733
  simp only [CollatzResearch.WordTrace]
  refine ⟨121773596613348026044756853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81182397742232017363171235 121773596613348026044756853)
  ·
    refine ⟨11416274682501377441695955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121773596613348026044756853 11416274682501377441695955)
    ·
      refine ⟨17124412023752066162543933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11416274682501377441695955 17124412023752066162543933)
      ·
        refine ⟨6421654508907024810953975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17124412023752066162543933 6421654508907024810953975)
        ·
          refine ⟨9632481763360537216430963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6421654508907024810953975 9632481763360537216430963)
          ·
            refine ⟨14448722645040805824646445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9632481763360537216430963 14448722645040805824646445)
            ·
              refine ⟨5418270991890302184242417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14448722645040805824646445 5418270991890302184242417)
              ·
                refine ⟨4063703243917726638181813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5418270991890302184242417 4063703243917726638181813)
                ·
                  refine ⟨380972179117286872329545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063703243917726638181813 380972179117286872329545)
                  ·
                    rfl

theorem cell22_3338733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3338733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338733 prefixEnd_3338733 := by exact prefixLift 3338733
  have htrace : WordTrace (prefixWord ++ tailWord_3338733) baseStart_3338733 baseEnd_3338733 := by
    simpa [prefixWord, tailWord_3338733, baseEnd_3338733] using wordTrace_append hprefix tailTrace_3338733
  have hstable : (prefixWord ++ tailWord_3338733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338733).length < 2 ^ (prefixWord ++ tailWord_3338733).sum := by decide
  have hdescent : baseEnd_3338733 < baseStart_3338733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338763 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 1, 4]
def baseStart_3338763 : Nat := 118140960795 + 3338763 * 2 ^ 59
def prefixEnd_3338763 : Nat := 4983230072969 + 3 ^ 40 * 3338763 * 2
def baseEnd_3338763 : Nat := 1142926806964950538738543

theorem tailTrace_3338763 : CollatzResearch.WordTrace tailWord_3338763 prefixEnd_3338763 1142926806964950538738543 := by
  unfold tailWord_3338763
  simp only [CollatzResearch.WordTrace]
  refine ⟨121774690803239341168348943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81183127202159560778899295 121774690803239341168348943)
  ·
    refine ⟨182662036204859011752523415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121774690803239341168348943 182662036204859011752523415)
    ·
      refine ⟨273993054307288517628785123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182662036204859011752523415 273993054307288517628785123)
      ·
        refine ⟨410989581460932776443177685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273993054307288517628785123 410989581460932776443177685)
        ·
          refine ⟨9632568315490611947886977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 410989581460932776443177685 9632568315490611947886977)
          ·
            refine ⟨7224426236617958960915233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9632568315490611947886977 7224426236617958960915233)
            ·
              refine ⟨5418319677463469220686425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7224426236617958960915233 5418319677463469220686425)
              ·
                refine ⟨4063739758097601915514819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5418319677463469220686425 4063739758097601915514819)
                ·
                  refine ⟨6095609637146402873272229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063739758097601915514819 6095609637146402873272229)
                  ·
                    refine ⟨1142926806964950538738543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095609637146402873272229 1142926806964950538738543)
                    ·
                      rfl

theorem cell22_3338763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 4].length) (baseStart_3338763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338763 prefixEnd_3338763 := by exact prefixLift 3338763
  have htrace : WordTrace (prefixWord ++ tailWord_3338763) baseStart_3338763 baseEnd_3338763 := by
    simpa [prefixWord, tailWord_3338763, baseEnd_3338763] using wordTrace_append hprefix tailTrace_3338763
  have hstable : (prefixWord ++ tailWord_3338763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338763).length < 2 ^ (prefixWord ++ tailWord_3338763).sum := by decide
  have hdescent : baseEnd_3338763 < baseStart_3338763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338778 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_3338778 : Nat := 118140960795 + 3338778 * 2 ^ 59
def prefixEnd_3338778 : Nat := 4983230072969 + 3 ^ 40 * 3338778 * 2
def baseEnd_3338778 : Nat := 380977313923831833204499

theorem tailTrace_3338778 : CollatzResearch.WordTrace tailWord_3338778 prefixEnd_3338778 380977313923831833204499 := by
  unfold tailWord_3338778
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443809474546249682536247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81183491932123332486763325 30443809474546249682536247)
  ·
    refine ⟨45665714211819374523804371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30443809474546249682536247 45665714211819374523804371)
    ·
      refine ⟨68498571317729061785706557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45665714211819374523804371 68498571317729061785706557)
      ·
        refine ⟨25686964244148398169639959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68498571317729061785706557 25686964244148398169639959)
        ·
          refine ⟨38530446366222597254459939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25686964244148398169639959 38530446366222597254459939)
          ·
            refine ⟨57795669549333895881689909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38530446366222597254459939 57795669549333895881689909)
            ·
              refine ⟨5418344020250052738908429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57795669549333895881689909 5418344020250052738908429)
              ·
                refine ⟨2031879007593769777090661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5418344020250052738908429 2031879007593769777090661)
                ·
                  refine ⟨380977313923831833204499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031879007593769777090661 380977313923831833204499)
                  ·
                    rfl

theorem cell22_3338778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_3338778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338778 prefixEnd_3338778 := by exact prefixLift 3338778
  have htrace : WordTrace (prefixWord ++ tailWord_3338778) baseStart_3338778 baseEnd_3338778 := by
    simpa [prefixWord, tailWord_3338778, baseEnd_3338778] using wordTrace_append hprefix tailTrace_3338778
  have hstable : (prefixWord ++ tailWord_3338778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338778).length < 2 ^ (prefixWord ++ tailWord_3338778).sum := by decide
  have hdescent : baseEnd_3338778 < baseStart_3338778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338789 : List Nat := [1, 3, 1, 2, 2, 1, 12]
def baseStart_3338789 : Nat := 118140960795 + 3338789 * 2 ^ 59
def prefixEnd_3338789 : Nat := 4983230072969 + 3 ^ 40 * 3338789 * 2
def baseEnd_3338789 : Nat := 42330952122085005095869

theorem tailTrace_3338789 : CollatzResearch.WordTrace tailWord_3338789 prefixEnd_3338789 42330952122085005095869 := by
  unfold tailWord_3338789
  simp only [CollatzResearch.WordTrace]
  refine ⟨121775639101145147608795421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81183759400763431739196947 121775639101145147608795421)
  ·
    refine ⟨45665864662929430353298283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121775639101145147608795421 45665864662929430353298283)
    ·
      refine ⟨68498796994394145529947425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45665864662929430353298283 68498796994394145529947425)
      ·
        refine ⟨51374097745795609147460569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68498796994394145529947425 51374097745795609147460569)
        ·
          refine ⟨38530573309346706860595427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51374097745795609147460569 38530573309346706860595427)
          ·
            refine ⟨57795859964020060290893141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38530573309346706860595427 57795859964020060290893141)
            ·
              refine ⟨42330952122085005095869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 57795859964020060290893141 42330952122085005095869)
              ·
                rfl

theorem cell22_3338789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 12].length) (baseStart_3338789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338789 prefixEnd_3338789 := by exact prefixLift 3338789
  have htrace : WordTrace (prefixWord ++ tailWord_3338789) baseStart_3338789 baseEnd_3338789 := by
    simpa [prefixWord, tailWord_3338789, baseEnd_3338789] using wordTrace_append hprefix tailTrace_3338789
  have hstable : (prefixWord ++ tailWord_3338789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338789).length < 2 ^ (prefixWord ++ tailWord_3338789).sum := by decide
  have hdescent : baseEnd_3338789 < baseStart_3338789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338810 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_3338810 : Nat := 118140960795 + 3338810 * 2 ^ 59
def prefixEnd_3338810 : Nat := 4983230072969 + 3 ^ 40 * 3338810 * 2
def baseEnd_3338810 : Nat := 1142942896025458082813399

theorem tailTrace_3338810 : CollatzResearch.WordTrace tailWord_3338810 prefixEnd_3338810 1142942896025458082813399 := by
  unfold tailWord_3338810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30444101258517267048827471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81184270022712712130206589 30444101258517267048827471)
  ·
    refine ⟨45666151887775900573241207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30444101258517267048827471 45666151887775900573241207)
    ·
      refine ⟨68499227831663850859861811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45666151887775900573241207 68499227831663850859861811)
      ·
        refine ⟨102748841747495776289792717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68499227831663850859861811 102748841747495776289792717)
        ·
          refine ⟨38530815655310916108672269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102748841747495776289792717 38530815655310916108672269)
          ·
            refine ⟨14449055870741593540752101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38530815655310916108672269 14449055870741593540752101)
            ·
              refine ⟨2709197975764048788891019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14449055870741593540752101 2709197975764048788891019)
              ·
                refine ⟨4063796963646073183336529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709197975764048788891019 4063796963646073183336529)
                ·
                  refine ⟨3047847722734554887502397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4063796963646073183336529 3047847722734554887502397)
                  ·
                    refine ⟨1142942896025458082813399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3047847722734554887502397 1142942896025458082813399)
                    ·
                      rfl

theorem cell22_3338810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_3338810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338810 prefixEnd_3338810 := by exact prefixLift 3338810
  have htrace : WordTrace (prefixWord ++ tailWord_3338810) baseStart_3338810 baseEnd_3338810 := by
    simpa [prefixWord, tailWord_3338810, baseEnd_3338810] using wordTrace_append hprefix tailTrace_3338810
  have hstable : (prefixWord ++ tailWord_3338810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338810).length < 2 ^ (prefixWord ++ tailWord_3338810).sum := by decide
  have hdescent : baseEnd_3338810 < baseStart_3338810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338814 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_3338814 : Nat := 118140960795 + 3338814 * 2 ^ 59
def prefixEnd_3338814 : Nat := 4983230072969 + 3 ^ 40 * 3338814 * 2
def baseEnd_3338814 : Nat := 1142944265307203405713387

theorem tailTrace_3338814 : CollatzResearch.WordTrace tailWord_3338814 prefixEnd_3338814 1142944265307203405713387 := by
  unfold tailWord_3338814
  simp only [CollatzResearch.WordTrace]
  refine ⟨15222068865756822109806937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81184367284036384585636997 15222068865756822109806937)
  ·
    refine ⟨11416551649317616582355203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15222068865756822109806937 11416551649317616582355203)
    ·
      refine ⟨17124827473976424873532805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11416551649317616582355203 17124827473976424873532805)
      ·
        refine ⟨3210905151370579663787401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17124827473976424873532805 3210905151370579663787401)
        ·
          refine ⟨2408178863527934747840551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210905151370579663787401 2408178863527934747840551)
          ·
            refine ⟨3612268295291902121760827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408178863527934747840551 3612268295291902121760827)
            ·
              refine ⟨5418402442937853182641241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612268295291902121760827 5418402442937853182641241)
              ·
                refine ⟨4063801832203389886980931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5418402442937853182641241 4063801832203389886980931)
                ·
                  refine ⟨6095702748305084830471397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063801832203389886980931 6095702748305084830471397)
                  ·
                    refine ⟨1142944265307203405713387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095702748305084830471397 1142944265307203405713387)
                    ·
                      rfl

theorem cell22_3338814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_3338814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338814 prefixEnd_3338814 := by exact prefixLift 3338814
  have htrace : WordTrace (prefixWord ++ tailWord_3338814) baseStart_3338814 baseEnd_3338814 := by
    simpa [prefixWord, tailWord_3338814, baseEnd_3338814] using wordTrace_append hprefix tailTrace_3338814
  have hstable : (prefixWord ++ tailWord_3338814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338814).length < 2 ^ (prefixWord ++ tailWord_3338814).sum := by decide
  have hdescent : baseEnd_3338814 < baseStart_3338814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338958 : List Nat := [4, 1, 1, 1, 3, 4, 8]
def baseStart_3338958 : Nat := 118140960795 + 3338958 * 2 ^ 59
def prefixEnd_3338958 : Nat := 4983230072969 + 3 ^ 40 * 3338958 * 2
def baseEnd_3338958 : Nat := 42333094794445741856035

theorem tailTrace_3338958 : CollatzResearch.WordTrace tailWord_3338958 prefixEnd_3338958 42333094794445741856035 := by
  unfold tailWord_3338958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15222725379691611183962191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81187868691688592981131685 15222725379691611183962191)
  ·
    refine ⟨22834088069537416775943287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15222725379691611183962191 22834088069537416775943287)
    ·
      refine ⟨34251132104306125163914931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22834088069537416775943287 34251132104306125163914931)
      ·
        refine ⟨51376698156459187745872397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34251132104306125163914931 51376698156459187745872397)
        ·
          refine ⟨19266261808672195404702149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51376698156459187745872397 19266261808672195404702149)
          ·
            refine ⟨3612424089126036638381653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19266261808672195404702149 3612424089126036638381653)
            ·
              refine ⟨42333094794445741856035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3612424089126036638381653 42333094794445741856035)
              ·
                rfl

theorem cell22_3338958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 8].length) (baseStart_3338958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338958 prefixEnd_3338958 := by exact prefixLift 3338958
  have htrace : WordTrace (prefixWord ++ tailWord_3338958) baseStart_3338958 baseEnd_3338958 := by
    simpa [prefixWord, tailWord_3338958, baseEnd_3338958] using wordTrace_append hprefix tailTrace_3338958
  have hstable : (prefixWord ++ tailWord_3338958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338958).length < 2 ^ (prefixWord ++ tailWord_3338958).sum := by decide
  have hdescent : baseEnd_3338958 < baseStart_3338958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338964 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3338964 : Nat := 118140960795 + 3338964 * 2 ^ 59
def prefixEnd_3338964 : Nat := 4983230072969 + 3 ^ 40 * 3338964 * 2
def baseEnd_3338964 : Nat := 380998537790884338154309

theorem tailTrace_3338964 : CollatzResearch.WordTrace tailWord_3338964 prefixEnd_3338964 380998537790884338154309 := by
  unfold tailWord_3338964
  simp only [CollatzResearch.WordTrace]
  refine ⟨60891010937755576248207973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81188014583674101664277297 60891010937755576248207973)
  ·
    refine ⟨11417064550829170546538995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60891010937755576248207973 11417064550829170546538995)
    ·
      refine ⟨17125596826243755819808493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11417064550829170546538995 17125596826243755819808493)
      ·
        refine ⟨6422098809841408432428185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17125596826243755819808493 6422098809841408432428185)
        ·
          refine ⟨4816574107381056324321139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6422098809841408432428185 4816574107381056324321139)
          ·
            refine ⟨7224861161071584486481709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816574107381056324321139 7224861161071584486481709)
            ·
              refine ⟨2709322935401844182430641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7224861161071584486481709 2709322935401844182430641)
              ·
                refine ⟨2031992201551383136822981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2709322935401844182430641 2031992201551383136822981)
                ·
                  refine ⟨380998537790884338154309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031992201551383136822981 380998537790884338154309)
                  ·
                    rfl

theorem cell22_3338964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3338964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338964 prefixEnd_3338964 := by exact prefixLift 3338964
  have htrace : WordTrace (prefixWord ++ tailWord_3338964) baseStart_3338964 baseEnd_3338964 := by
    simpa [prefixWord, tailWord_3338964, baseEnd_3338964] using wordTrace_append hprefix tailTrace_3338964
  have hstable : (prefixWord ++ tailWord_3338964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338964).length < 2 ^ (prefixWord ++ tailWord_3338964).sum := by decide
  have hdescent : baseEnd_3338964 < baseStart_3338964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338979 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 2, 3]
def baseStart_3338979 : Nat := 118140960795 + 3338979 * 2 ^ 59
def prefixEnd_3338979 : Nat := 4983230072969 + 3 ^ 40 * 3338979 * 2
def baseEnd_3338979 : Nat := 1143000748179197975337881

theorem tailTrace_3338979 : CollatzResearch.WordTrace tailWord_3338979 prefixEnd_3338979 1143000748179197975337881 := by
  unfold tailWord_3338979
  simp only [CollatzResearch.WordTrace]
  refine ⟨121782568970456810058211991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81188379313637873372141327 121782568970456810058211991)
  ·
    refine ⟨182673853455685215087317987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121782568970456810058211991 182673853455685215087317987)
    ·
      refine ⟨274010780183527822630976981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182673853455685215087317987 274010780183527822630976981)
      ·
        refine ⟨6422127660551433342913523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 274010780183527822630976981 6422127660551433342913523)
        ·
          refine ⟨9633191490827150014370285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422127660551433342913523 9633191490827150014370285)
          ·
            refine ⟨3612446809060181255388857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9633191490827150014370285 3612446809060181255388857)
            ·
              refine ⟨2709335106795135941541643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612446809060181255388857 2709335106795135941541643)
              ·
                refine ⟨4064002660192703912312465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709335106795135941541643 4064002660192703912312465)
                ·
                  refine ⟨3048001995144527934234349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064002660192703912312465 3048001995144527934234349)
                  ·
                    refine ⟨1143000748179197975337881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048001995144527934234349 1143000748179197975337881)
                    ·
                      rfl

theorem cell22_3338979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 3].length) (baseStart_3338979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3338979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3338979 prefixEnd_3338979 := by exact prefixLift 3338979
  have htrace : WordTrace (prefixWord ++ tailWord_3338979) baseStart_3338979 baseEnd_3338979 := by
    simpa [prefixWord, tailWord_3338979, baseEnd_3338979] using wordTrace_append hprefix tailTrace_3338979
  have hstable : (prefixWord ++ tailWord_3338979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338979).length < 2 ^ (prefixWord ++ tailWord_3338979).sum := by decide
  have hdescent : baseEnd_3338979 < baseStart_3338979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339018 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_3339018 : Nat := 118140960795 + 3339018 * 2 ^ 59
def prefixEnd_3339018 : Nat := 4983230072969 + 3 ^ 40 * 3339018 * 2
def baseEnd_3339018 : Nat := 1143014098676214873612761

theorem tailTrace_3339018 : CollatzResearch.WordTrace tailWord_3339018 prefixEnd_3339018 1143014098676214873612761 := by
  unfold tailWord_3339018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445997854328879929720427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81189327611543679812587805 30445997854328879929720427)
  ·
    refine ⟨45668996781493319894580641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30445997854328879929720427 45668996781493319894580641)
    ·
      refine ⟨34251747586119989920935481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45668996781493319894580641 34251747586119989920935481)
      ·
        refine ⟨25688810689589992440701611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34251747586119989920935481 25688810689589992440701611)
        ·
          refine ⟨38533216034384988661052417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25688810689589992440701611 38533216034384988661052417)
          ·
            refine ⟨28899912025788741495789313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38533216034384988661052417 28899912025788741495789313)
            ·
              refine ⟨21674934019341556121841985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28899912025788741495789313 21674934019341556121841985)
              ·
                refine ⟨16256200514506167091381489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21674934019341556121841985 16256200514506167091381489)
                ·
                  refine ⟨12192150385879625318536117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16256200514506167091381489 12192150385879625318536117)
                  ·
                    refine ⟨1143014098676214873612761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192150385879625318536117 1143014098676214873612761)
                    ·
                      rfl

theorem cell22_3339018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_3339018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339018 prefixEnd_3339018 := by exact prefixLift 3339018
  have htrace : WordTrace (prefixWord ++ tailWord_3339018) baseStart_3339018 baseEnd_3339018 := by
    simpa [prefixWord, tailWord_3339018, baseEnd_3339018] using wordTrace_append hprefix tailTrace_3339018
  have hstable : (prefixWord ++ tailWord_3339018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339018).length < 2 ^ (prefixWord ++ tailWord_3339018).sum := by decide
  have hdescent : baseEnd_3339018 < baseStart_3339018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339063 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3339063 : Nat := 118140960795 + 3339063 * 2 ^ 59
def prefixEnd_3339063 : Nat := 4983230072969 + 3 ^ 40 * 3339063 * 2
def baseEnd_3339063 : Nat := 1143029503095849756237623

theorem tailTrace_3339063 : CollatzResearch.WordTrace tailWord_3339063 prefixEnd_3339063 1143029503095849756237623 := by
  unfold tailWord_3339063
  simp only [CollatzResearch.WordTrace]
  refine ⟨121785632702152492404269843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81190421801434994936179895 121785632702152492404269843)
  ·
    refine ⟨182678449053228738606404765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121785632702152492404269843 182678449053228738606404765)
    ·
      refine ⟨68504418394960776977401787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182678449053228738606404765 68504418394960776977401787)
      ·
        refine ⟨102756627592441165466102681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68504418394960776977401787 102756627592441165466102681)
        ·
          refine ⟨77067470694330874099577011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102756627592441165466102681 77067470694330874099577011)
          ·
            refine ⟨115601206041496311149365517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77067470694330874099577011 115601206041496311149365517)
            ·
              refine ⟨43350452265561116681012069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115601206041496311149365517 43350452265561116681012069)
              ·
                refine ⟨8128209799792709377689763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43350452265561116681012069 8128209799792709377689763)
                ·
                  refine ⟨12192314699689064066534645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128209799792709377689763 12192314699689064066534645)
                  ·
                    refine ⟨1143029503095849756237623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192314699689064066534645 1143029503095849756237623)
                    ·
                      rfl

theorem cell22_3339063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3339063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339063 prefixEnd_3339063 := by exact prefixLift 3339063
  have htrace : WordTrace (prefixWord ++ tailWord_3339063) baseStart_3339063 baseEnd_3339063 := by
    simpa [prefixWord, tailWord_3339063, baseEnd_3339063] using wordTrace_append hprefix tailTrace_3339063
  have hstable : (prefixWord ++ tailWord_3339063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339063).length < 2 ^ (prefixWord ++ tailWord_3339063).sum := by decide
  have hdescent : baseEnd_3339063 < baseStart_3339063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339080 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_3339080 : Nat := 118140960795 + 3339080 * 2 ^ 59
def prefixEnd_3339080 : Nat := 4983230072969 + 3 ^ 40 * 3339080 * 2
def baseEnd_3339080 : Nat := 1143035322543267378562571

theorem tailTrace_3339080 : CollatzResearch.WordTrace tailWord_3339080 prefixEnd_3339080 1143035322543267378562571 := by
  unfold tailWord_3339080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60893126371545452153819347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81190835162060602871759129 60893126371545452153819347)
  ·
    refine ⟨91339689557318178230729021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60893126371545452153819347 91339689557318178230729021)
    ·
      refine ⟨34252383583994316836523383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91339689557318178230729021 34252383583994316836523383)
      ·
        refine ⟨51378575375991475254785075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34252383583994316836523383 51378575375991475254785075)
        ·
          refine ⟨77067863063987212882177613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51378575375991475254785075 77067863063987212882177613)
          ·
            refine ⟨28900448648995204830816605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77067863063987212882177613 28900448648995204830816605)
            ·
              refine ⟨10837668243373201811556227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28900448648995204830816605 10837668243373201811556227)
              ·
                refine ⟨16256502365059802717334341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837668243373201811556227 16256502365059802717334341)
                ·
                  refine ⟨3048094193448713009500189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16256502365059802717334341 3048094193448713009500189)
                  ·
                    refine ⟨1143035322543267378562571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048094193448713009500189 1143035322543267378562571)
                    ·
                      rfl

theorem cell22_3339080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_3339080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339080 prefixEnd_3339080 := by exact prefixLift 3339080
  have htrace : WordTrace (prefixWord ++ tailWord_3339080) baseStart_3339080 baseEnd_3339080 := by
    simpa [prefixWord, tailWord_3339080, baseEnd_3339080] using wordTrace_append hprefix tailTrace_3339080
  have hstable : (prefixWord ++ tailWord_3339080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339080).length < 2 ^ (prefixWord ++ tailWord_3339080).sum := by decide
  have hdescent : baseEnd_3339080 < baseStart_3339080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339093 : List Nat := [1, 3, 2, 2, 2, 1, 2, 9]
def baseStart_3339093 : Nat := 118140960795 + 3339093 * 2 ^ 59
def prefixEnd_3339093 : Nat := 4983230072969 + 3 ^ 40 * 3339093 * 2
def baseEnd_3339093 : Nat := 127004419189882186443059

theorem tailTrace_3339093 : CollatzResearch.WordTrace tailWord_3339093 prefixEnd_3339093 127004419189882186443059 := by
  unfold tailWord_3339093
  simp only [CollatzResearch.WordTrace]
  refine ⟨121786726892043807527861933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81191151261362538351907955 121786726892043807527861933)
  ·
    refine ⟨45670022584516427822948225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121786726892043807527861933 45670022584516427822948225)
    ·
      refine ⟨34252516938387320867211169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45670022584516427822948225 34252516938387320867211169)
      ·
        refine ⟨25689387703790490650408377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34252516938387320867211169 25689387703790490650408377)
        ·
          refine ⟨19267040777842867987806283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25689387703790490650408377 19267040777842867987806283)
          ·
            refine ⟨28900561166764301981709425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19267040777842867987806283 28900561166764301981709425)
            ·
              refine ⟨21675420875073226486282069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28900561166764301981709425 21675420875073226486282069)
              ·
                refine ⟨127004419189882186443059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21675420875073226486282069 127004419189882186443059)
                ·
                  rfl

theorem cell22_3339093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 9].length) (baseStart_3339093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339093 prefixEnd_3339093 := by exact prefixLift 3339093
  have htrace : WordTrace (prefixWord ++ tailWord_3339093) baseStart_3339093 baseEnd_3339093 := by
    simpa [prefixWord, tailWord_3339093, baseEnd_3339093] using wordTrace_append hprefix tailTrace_3339093
  have hstable : (prefixWord ++ tailWord_3339093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339093).length < 2 ^ (prefixWord ++ tailWord_3339093).sum := by decide
  have hdescent : baseEnd_3339093 < baseStart_3339093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339153 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3339153 : Nat := 118140960795 + 3339153 * 2 ^ 59
def prefixEnd_3339153 : Nat := 4983230072969 + 3 ^ 40 * 3339153 * 2
def baseEnd_3339153 : Nat := 1143060311935119521487347

theorem tailTrace_3339153 : CollatzResearch.WordTrace tailWord_3339153 prefixEnd_3339153 1143060311935119521487347 := by
  unfold tailWord_3339153
  simp only [CollatzResearch.WordTrace]
  refine ⟨121788915271826437775046113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81192610181217625183364075 121788915271826437775046113)
  ·
    refine ⟨91341686453869828331284585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121788915271826437775046113 91341686453869828331284585)
    ·
      refine ⟨68506264840402371248463439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91341686453869828331284585 68506264840402371248463439)
      ·
        refine ⟨102759397260603556872695159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68506264840402371248463439 102759397260603556872695159)
        ·
          refine ⟨154139095890905335309042739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102759397260603556872695159 154139095890905335309042739)
          ·
            refine ⟨231208643836358002963564109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154139095890905335309042739 231208643836358002963564109)
            ·
              refine ⟨86703241438634251111336541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231208643836358002963564109 86703241438634251111336541)
              ·
                refine ⟨32513715539487844166751203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86703241438634251111336541 32513715539487844166751203)
                ·
                  refine ⟨48770573309231766250126805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32513715539487844166751203 48770573309231766250126805)
                  ·
                    refine ⟨1143060311935119521487347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48770573309231766250126805 1143060311935119521487347)
                    ·
                      rfl

theorem cell22_3339153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3339153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339153 prefixEnd_3339153 := by exact prefixLift 3339153
  have htrace : WordTrace (prefixWord ++ tailWord_3339153) baseStart_3339153 baseEnd_3339153 := by
    simpa [prefixWord, tailWord_3339153, baseEnd_3339153] using wordTrace_append hprefix tailTrace_3339153
  have hstable : (prefixWord ++ tailWord_3339153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339153).length < 2 ^ (prefixWord ++ tailWord_3339153).sum := by decide
  have hdescent : baseEnd_3339153 < baseStart_3339153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339183 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 10]
def baseStart_3339183 : Nat := 118140960795 + 3339183 * 2 ^ 59
def prefixEnd_3339183 : Nat := 4983230072969 + 3 ^ 40 * 3339183 * 2
def baseEnd_3339183 : Nat := 381023527182736481079085

theorem tailTrace_3339183 : CollatzResearch.WordTrace tailWord_3339183 prefixEnd_3339183 381023527182736481079085 := by
  unfold tailWord_3339183
  simp only [CollatzResearch.WordTrace]
  refine ⟨121790009461717752898638203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81193339641145168599092135 121790009461717752898638203)
  ·
    refine ⟨182685014192576629347957305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121790009461717752898638203 182685014192576629347957305)
    ·
      refine ⟨137013760644432472010967979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182685014192576629347957305 137013760644432472010967979)
      ·
        refine ⟨205520640966648708016451969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137013760644432472010967979 205520640966648708016451969)
        ·
          refine ⟨154140480724986531012338977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205520640966648708016451969 154140480724986531012338977)
          ·
            refine ⟨115605360543739898259254233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154140480724986531012338977 115605360543739898259254233)
            ·
              refine ⟨86704020407804923694440675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115605360543739898259254233 86704020407804923694440675)
              ·
                refine ⟨130056030611707385541661013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86704020407804923694440675 130056030611707385541661013)
                ·
                  refine ⟨381023527182736481079085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130056030611707385541661013 381023527182736481079085)
                  ·
                    rfl

theorem cell22_3339183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_3339183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339183 prefixEnd_3339183 := by exact prefixLift 3339183
  have htrace : WordTrace (prefixWord ++ tailWord_3339183) baseStart_3339183 baseEnd_3339183 := by
    simpa [prefixWord, tailWord_3339183, baseEnd_3339183] using wordTrace_append hprefix tailTrace_3339183
  have hstable : (prefixWord ++ tailWord_3339183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339183).length < 2 ^ (prefixWord ++ tailWord_3339183).sum := by decide
  have hdescent : baseEnd_3339183 < baseStart_3339183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339204 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3339204 : Nat := 118140960795 + 3339204 * 2 ^ 59
def prefixEnd_3339204 : Nat := 4983230072969 + 3 ^ 40 * 3339204 * 2
def baseEnd_3339204 : Nat := 1143077770277372388462191

theorem tailTrace_3339204 : CollatzResearch.WordTrace tailWord_3339204 prefixEnd_3339204 1143077770277372388462191 := by
  unfold tailWord_3339204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60895387697320836742576333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81193850263094448990101777 60895387697320836742576333)
  ·
    refine ⟨22835770386495313778466125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60895387697320836742576333 22835770386495313778466125)
    ·
      refine ⟨8563413894935742666924797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22835770386495313778466125 8563413894935742666924797)
      ·
        refine ⟨3211280210600903500096799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8563413894935742666924797 3211280210600903500096799)
        ·
          refine ⟨4816920315901355250145199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211280210600903500096799 4816920315901355250145199)
          ·
            refine ⟨7225380473852032875217799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816920315901355250145199 7225380473852032875217799)
            ·
              refine ⟨10838070710778049312826699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7225380473852032875217799 10838070710778049312826699)
              ·
                refine ⟨16257106066167073969240049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10838070710778049312826699 16257106066167073969240049)
                ·
                  refine ⟨12192829549625305476930037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16257106066167073969240049 12192829549625305476930037)
                  ·
                    refine ⟨1143077770277372388462191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192829549625305476930037 1143077770277372388462191)
                    ·
                      rfl

theorem cell22_3339204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3339204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339204 prefixEnd_3339204 := by exact prefixLift 3339204
  have htrace : WordTrace (prefixWord ++ tailWord_3339204) baseStart_3339204 baseEnd_3339204 := by
    simpa [prefixWord, tailWord_3339204, baseEnd_3339204] using wordTrace_append hprefix tailTrace_3339204
  have hstable : (prefixWord ++ tailWord_3339204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339204).length < 2 ^ (prefixWord ++ tailWord_3339204).sum := by decide
  have hdescent : baseEnd_3339204 < baseStart_3339204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339215 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 1, 5]
def baseStart_3339215 : Nat := 118140960795 + 3339215 * 2 ^ 59
def prefixEnd_3339215 : Nat := 4983230072969 + 3 ^ 40 * 3339215 * 2
def baseEnd_3339215 : Nat := 1143081535802172026437157

theorem tailTrace_3339215 : CollatzResearch.WordTrace tailWord_3339215 prefixEnd_3339215 1143081535802172026437157 := by
  unfold tailWord_3339215
  simp only [CollatzResearch.WordTrace]
  refine ⟨121791176597601822363803099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81194117731734548242535399 121791176597601822363803099)
  ·
    refine ⟨182686764896402733545704649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121791176597601822363803099 182686764896402733545704649)
    ·
      refine ⟨137015073672302050159278487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182686764896402733545704649 137015073672302050159278487)
      ·
        refine ⟨205522610508453075238917731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137015073672302050159278487 205522610508453075238917731)
        ·
          refine ⟨308283915762679612858376597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205522610508453075238917731 308283915762679612858376597)
          ·
            refine ⟨14450808551375606852736403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308283915762679612858376597 14450808551375606852736403)
            ·
              refine ⟨21676212827063410279104605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14450808551375606852736403 21676212827063410279104605)
              ·
                refine ⟨8128579810148778854664227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21676212827063410279104605 8128579810148778854664227)
                ·
                  refine ⟨12192869715223168281996341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128579810148778854664227 12192869715223168281996341)
                  ·
                    refine ⟨1143081535802172026437157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192869715223168281996341 1143081535802172026437157)
                    ·
                      rfl

theorem cell22_3339215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_3339215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339215 prefixEnd_3339215 := by exact prefixLift 3339215
  have htrace : WordTrace (prefixWord ++ tailWord_3339215) baseStart_3339215 baseEnd_3339215 := by
    simpa [prefixWord, tailWord_3339215, baseEnd_3339215] using wordTrace_append hprefix tailTrace_3339215
  have hstable : (prefixWord ++ tailWord_3339215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339215).length < 2 ^ (prefixWord ++ tailWord_3339215).sum := by decide
  have hdescent : baseEnd_3339215 < baseStart_3339215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339249 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_3339249 : Nat := 118140960795 + 3339249 * 2 ^ 59
def prefixEnd_3339249 : Nat := 4983230072969 + 3 ^ 40 * 3339249 * 2
def baseEnd_3339249 : Nat := 1143093174697007271087053

theorem tailTrace_3339249 : CollatzResearch.WordTrace tailWord_3339249 prefixEnd_3339249 1143093174697007271087053 := by
  unfold tailWord_3339249
  simp only [CollatzResearch.WordTrace]
  refine ⟨121792416679478646170540801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81194944452985764113693867 121792416679478646170540801)
  ·
    refine ⟨91344312509608984627905601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121792416679478646170540801 91344312509608984627905601)
    ·
      refine ⟨68508234382206738470929201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91344312509608984627905601 68508234382206738470929201)
      ·
        refine ⟨51381175786655053853196901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68508234382206738470929201 51381175786655053853196901)
        ·
          refine ⟨9633970459997822597474419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51381175786655053853196901 9633970459997822597474419)
          ·
            refine ⟨14450955689996733896211629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633970459997822597474419 14450955689996733896211629)
            ·
              refine ⟨5419108383748775211079361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14450955689996733896211629 5419108383748775211079361)
              ·
                refine ⟨4064331287811581408309521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419108383748775211079361 4064331287811581408309521)
                ·
                  refine ⟨3048248465858686056232141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064331287811581408309521 3048248465858686056232141)
                  ·
                    refine ⟨1143093174697007271087053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048248465858686056232141 1143093174697007271087053)
                    ·
                      rfl

theorem cell22_3339249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_3339249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339249 prefixEnd_3339249 := by exact prefixLift 3339249
  have htrace : WordTrace (prefixWord ++ tailWord_3339249) baseStart_3339249 baseEnd_3339249 := by
    simpa [prefixWord, tailWord_3339249, baseEnd_3339249] using wordTrace_append hprefix tailTrace_3339249
  have hstable : (prefixWord ++ tailWord_3339249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339249).length < 2 ^ (prefixWord ++ tailWord_3339249).sum := by decide
  have hdescent : baseEnd_3339249 < baseStart_3339249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339290 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_3339290 : Nat := 118140960795 + 3339290 * 2 ^ 59
def prefixEnd_3339290 : Nat := 4983230072969 + 3 ^ 40 * 3339290 * 2
def baseEnd_3339290 : Nat := 381035736611632276937309

theorem tailTrace_3339290 : CollatzResearch.WordTrace tailWord_3339290 prefixEnd_3339290 381035736611632276937309 := by
  unfold tailWord_3339290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30448478018082527543195831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81195941381553406781855549 30448478018082527543195831)
  ·
    refine ⟨45672717027123791314793747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30448478018082527543195831 45672717027123791314793747)
    ·
      refine ⟨68509075540685686972190621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45672717027123791314793747 68509075540685686972190621)
      ·
        refine ⟨25690903327757132614571483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68509075540685686972190621 25690903327757132614571483)
        ·
          refine ⟨38536354991635698921857225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25690903327757132614571483 38536354991635698921857225)
          ·
            refine ⟨28902266243726774191392919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38536354991635698921857225 28902266243726774191392919)
            ·
              refine ⟨43353399365590161287089379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28902266243726774191392919 43353399365590161287089379)
              ·
                refine ⟨65030099048385241930634069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43353399365590161287089379 65030099048385241930634069)
                ·
                  refine ⟨381035736611632276937309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65030099048385241930634069 381035736611632276937309)
                  ·
                    rfl

theorem cell22_3339290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_3339290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339290 prefixEnd_3339290 := by exact prefixLift 3339290
  have htrace : WordTrace (prefixWord ++ tailWord_3339290) baseStart_3339290 baseEnd_3339290 := by
    simpa [prefixWord, tailWord_3339290, baseEnd_3339290] using wordTrace_append hprefix tailTrace_3339290
  have hstable : (prefixWord ++ tailWord_3339290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339290).length < 2 ^ (prefixWord ++ tailWord_3339290).sum := by decide
  have hdescent : baseEnd_3339290 < baseStart_3339290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339324 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 5]
def baseStart_3339324 : Nat := 118140960795 + 3339324 * 2 ^ 59
def prefixEnd_3339324 : Nat := 4983230072969 + 3 ^ 40 * 3339324 * 2
def baseEnd_3339324 : Nat := 381039616243244025153941

theorem tailTrace_3339324 : CollatzResearch.WordTrace tailWord_3339324 prefixEnd_3339324 381039616243244025153941 := by
  unfold tailWord_3339324
  simp only [CollatzResearch.WordTrace]
  refine ⟨60897576077103466989760513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81196768102804622653014017 60897576077103466989760513)
  ·
    refine ⟨45673182057827600242320385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60897576077103466989760513 45673182057827600242320385)
    ·
      refine ⟨34254886543370700181740289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45673182057827600242320385 34254886543370700181740289)
      ·
        refine ⟨25691164907528025136305217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34254886543370700181740289 25691164907528025136305217)
        ·
          refine ⟨19268373680646018852228913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25691164907528025136305217 19268373680646018852228913)
          ·
            refine ⟨14451280260484514139171685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19268373680646018852228913 14451280260484514139171685)
            ·
              refine ⟨2709615048840846401094691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14451280260484514139171685 2709615048840846401094691)
              ·
                refine ⟨4064422573261269601642037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709615048840846401094691 4064422573261269601642037)
                ·
                  refine ⟨381039616243244025153941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064422573261269601642037 381039616243244025153941)
                  ·
                    rfl

theorem cell22_3339324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_3339324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339324 prefixEnd_3339324 := by exact prefixLift 3339324
  have htrace : WordTrace (prefixWord ++ tailWord_3339324) baseStart_3339324 baseEnd_3339324 := by
    simpa [prefixWord, tailWord_3339324, baseEnd_3339324] using wordTrace_append hprefix tailTrace_3339324
  have hstable : (prefixWord ++ tailWord_3339324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339324).length < 2 ^ (prefixWord ++ tailWord_3339324).sum := by decide
  have hdescent : baseEnd_3339324 < baseStart_3339324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339337 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_3339337 : Nat := 118140960795 + 3339337 * 2 ^ 59
def prefixEnd_3339337 : Nat := 4983230072969 + 3 ^ 40 * 3339337 * 2
def baseEnd_3339337 : Nat := 1143123298895404374886783

theorem tailTrace_3339337 : CollatzResearch.WordTrace tailWord_3339337 prefixEnd_3339337 1143123298895404374886783 := by
  unfold tailWord_3339337
  simp only [CollatzResearch.WordTrace]
  refine ⟨121795626303159837199744265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81197084202106558133162843 121795626303159837199744265)
  ·
    refine ⟨91346719727369877899808199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121795626303159837199744265 91346719727369877899808199)
    ·
      refine ⟨137020079591054816849712299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91346719727369877899808199 137020079591054816849712299)
      ·
        refine ⟨205530119386582225274568449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137020079591054816849712299 205530119386582225274568449)
        ·
          refine ⟨154147589539936668955926337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205530119386582225274568449 154147589539936668955926337)
          ·
            refine ⟨115610692154952501716944753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154147589539936668955926337 115610692154952501716944753)
            ·
              refine ⟨86708019116214376287708565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115610692154952501716944753 86708019116214376287708565)
              ·
                refine ⟨4064438396072548888486339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86708019116214376287708565 4064438396072548888486339)
                ·
                  refine ⟨6096657594108823332729509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064438396072548888486339 6096657594108823332729509)
                  ·
                    refine ⟨1143123298895404374886783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6096657594108823332729509 1143123298895404374886783)
                    ·
                      rfl

theorem cell22_3339337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_3339337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339337 prefixEnd_3339337 := by exact prefixLift 3339337
  have htrace : WordTrace (prefixWord ++ tailWord_3339337) baseStart_3339337 baseEnd_3339337 := by
    simpa [prefixWord, tailWord_3339337, baseEnd_3339337] using wordTrace_append hprefix tailTrace_3339337
  have hstable : (prefixWord ++ tailWord_3339337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339337).length < 2 ^ (prefixWord ++ tailWord_3339337).sum := by decide
  have hdescent : baseEnd_3339337 < baseStart_3339337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339358 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3339358 : Nat := 118140960795 + 3339358 * 2 ^ 59
def prefixEnd_3339358 : Nat := 4983230072969 + 3 ^ 40 * 3339358 * 2
def baseEnd_3339358 : Nat := 381043495874855773370573

theorem tailTrace_3339358 : CollatzResearch.WordTrace tailWord_3339358 prefixEnd_3339358 381043495874855773370573 := by
  unfold tailWord_3339358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15224549029510469723282341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81197594824055838524172485 15224549029510469723282341)
  ·
    refine ⟨2854602943033213073115439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15224549029510469723282341 2854602943033213073115439)
    ·
      refine ⟨4281904414549819609673159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854602943033213073115439 4281904414549819609673159)
      ·
        refine ⟨6422856621824729414509739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281904414549819609673159 6422856621824729414509739)
        ·
          refine ⟨9634284932737094121764609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422856621824729414509739 9634284932737094121764609)
          ·
            refine ⟨7225713699552820591323457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9634284932737094121764609 7225713699552820591323457)
            ·
              refine ⟨5419285274664615443492593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7225713699552820591323457 5419285274664615443492593)
              ·
                refine ⟨4064463955998461582619445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419285274664615443492593 4064463955998461582619445)
                ·
                  refine ⟨381043495874855773370573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064463955998461582619445 381043495874855773370573)
                  ·
                    rfl

theorem cell22_3339358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3339358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339358 prefixEnd_3339358 := by exact prefixLift 3339358
  have htrace : WordTrace (prefixWord ++ tailWord_3339358) baseStart_3339358 baseEnd_3339358 := by
    simpa [prefixWord, tailWord_3339358, baseEnd_3339358] using wordTrace_append hprefix tailTrace_3339358
  have hstable : (prefixWord ++ tailWord_3339358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339358).length < 2 ^ (prefixWord ++ tailWord_3339358).sum := by decide
  have hdescent : baseEnd_3339358 < baseStart_3339358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339369 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 4]
def baseStart_3339369 : Nat := 118140960795 + 3339369 * 2 ^ 59
def prefixEnd_3339369 : Nat := 4983230072969 + 3 ^ 40 * 3339369 * 2
def baseEnd_3339369 : Nat := 381044751049788986028895

theorem tailTrace_3339369 : CollatzResearch.WordTrace tailWord_3339369 prefixEnd_3339369 381044751049788986028895 := by
  unfold tailWord_3339369
  simp only [CollatzResearch.WordTrace]
  refine ⟨121796793439043906664909161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81197862292695937776606107 121796793439043906664909161)
  ·
    refine ⟨91347595079282929998681871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121796793439043906664909161 91347595079282929998681871)
    ·
      refine ⟨137021392618924394998022807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91347595079282929998681871 137021392618924394998022807)
      ·
        refine ⟨205532088928386592497034211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137021392618924394998022807 205532088928386592497034211)
        ·
          refine ⟨308298133392579888745551317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205532088928386592497034211 308298133392579888745551317)
          ·
            refine ⟨7225737501388591142473859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 308298133392579888745551317 7225737501388591142473859)
            ·
              refine ⟨10838606252082886713710789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7225737501388591142473859 10838606252082886713710789)
              ·
                refine ⟨2032238672265541258820773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10838606252082886713710789 2032238672265541258820773)
                ·
                  refine ⟨381044751049788986028895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2032238672265541258820773 381044751049788986028895)
                  ·
                    rfl

theorem cell22_3339369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_3339369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339369 prefixEnd_3339369 := by exact prefixLift 3339369
  have htrace : WordTrace (prefixWord ++ tailWord_3339369) baseStart_3339369 baseEnd_3339369 := by
    simpa [prefixWord, tailWord_3339369, baseEnd_3339369] using wordTrace_append hprefix tailTrace_3339369
  have hstable : (prefixWord ++ tailWord_3339369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339369).length < 2 ^ (prefixWord ++ tailWord_3339369).sum := by decide
  have hdescent : baseEnd_3339369 < baseStart_3339369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339384 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_3339384 : Nat := 118140960795 + 3339384 * 2 ^ 59
def prefixEnd_3339384 : Nat := 4983230072969 + 3 ^ 40 * 3339384 * 2
def baseEnd_3339384 : Nat := 1143139387955911918961639

theorem tailTrace_3339384 : CollatzResearch.WordTrace tailWord_3339384 prefixEnd_3339384 1143139387955911918961639 := by
  unfold tailWord_3339384
  simp only [CollatzResearch.WordTrace]
  refine ⟨60898670266994782113352603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81198227022659709484470137 60898670266994782113352603)
  ·
    refine ⟨91348005400492173170028905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60898670266994782113352603 91348005400492173170028905)
    ·
      refine ⟨68511004050369129877521679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91348005400492173170028905 68511004050369129877521679)
      ·
        refine ⟨102766506075553694816282519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68511004050369129877521679 102766506075553694816282519)
        ·
          refine ⟨154149759113330542224423779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102766506075553694816282519 154149759113330542224423779)
          ·
            refine ⟨231224638669995813336635669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154149759113330542224423779 231224638669995813336635669)
            ·
              refine ⟨10838654937656053750154797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231224638669995813336635669 10838654937656053750154797)
              ·
                refine ⟨4064495601621020156308049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10838654937656053750154797 4064495601621020156308049)
                ·
                  refine ⟨3048371701215765117231037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064495601621020156308049 3048371701215765117231037)
                  ·
                    refine ⟨1143139387955911918961639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048371701215765117231037 1143139387955911918961639)
                    ·
                      rfl

theorem cell22_3339384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_3339384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339384 prefixEnd_3339384 := by exact prefixLift 3339384
  have htrace : WordTrace (prefixWord ++ tailWord_3339384) baseStart_3339384 baseEnd_3339384 := by
    simpa [prefixWord, tailWord_3339384, baseEnd_3339384] using wordTrace_append hprefix tailTrace_3339384
  have hstable : (prefixWord ++ tailWord_3339384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339384).length < 2 ^ (prefixWord ++ tailWord_3339384).sum := by decide
  have hdescent : baseEnd_3339384 < baseStart_3339384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339418 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_3339418 : Nat := 118140960795 + 3339418 * 2 ^ 59
def prefixEnd_3339418 : Nat := 4983230072969 + 3 ^ 40 * 3339418 * 2
def baseEnd_3339418 : Nat := 1143151026850747163611535

theorem tailTrace_3339418 : CollatzResearch.WordTrace tailWord_3339418 prefixEnd_3339418 1143151026850747163611535 := by
  unfold tailWord_3339418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30449645153966597008360727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81199053743910925355628605 30449645153966597008360727)
  ·
    refine ⟨45674467730949895512541091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30449645153966597008360727 45674467730949895512541091)
    ·
      refine ⟨68511701596424843268811637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45674467730949895512541091 68511701596424843268811637)
      ·
        refine ⟨6422972024664829056451091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68511701596424843268811637 6422972024664829056451091)
        ·
          refine ⟨9634458036997243584676637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422972024664829056451091 9634458036997243584676637)
          ·
            refine ⟨3612921763873966344253739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9634458036997243584676637 3612921763873966344253739)
            ·
              refine ⟨5419382645810949516380609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612921763873966344253739 5419382645810949516380609)
              ·
                refine ⟨4064536984358212137285457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419382645810949516380609 4064536984358212137285457)
                ·
                  refine ⟨3048402738268659102964093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064536984358212137285457 3048402738268659102964093)
                  ·
                    refine ⟨1143151026850747163611535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048402738268659102964093 1143151026850747163611535)
                    ·
                      rfl

theorem cell22_3339418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_3339418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339418 prefixEnd_3339418 := by exact prefixLift 3339418
  have htrace : WordTrace (prefixWord ++ tailWord_3339418) baseStart_3339418 baseEnd_3339418 := by
    simpa [prefixWord, tailWord_3339418, baseEnd_3339418] using wordTrace_append hprefix tailTrace_3339418
  have hstable : (prefixWord ++ tailWord_3339418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339418).length < 2 ^ (prefixWord ++ tailWord_3339418).sum := by decide
  have hdescent : baseEnd_3339418 < baseStart_3339418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339429 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_3339429 : Nat := 118140960795 + 3339429 * 2 ^ 59
def prefixEnd_3339429 : Nat := 4983230072969 + 3 ^ 40 * 3339429 * 2
def baseEnd_3339429 : Nat := 1143154792375546801586501

theorem tailTrace_3339429 : CollatzResearch.WordTrace tailWord_3339429 prefixEnd_3339429 1143154792375546801586501 := by
  unfold tailWord_3339429
  simp only [CollatzResearch.WordTrace]
  refine ⟨121798981818826536912093341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81199321212551024608062227 121798981818826536912093341)
  ·
    refine ⟨45674618182059951342035003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121798981818826536912093341 45674618182059951342035003)
    ·
      refine ⟨68511927273089927013052505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45674618182059951342035003 68511927273089927013052505)
      ·
        refine ⟨51383945454817445259789379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68511927273089927013052505 51383945454817445259789379)
        ·
          refine ⟨77075918182226167889684069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51383945454817445259789379 77075918182226167889684069)
          ·
            refine ⟨14451734659167406479315763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77075918182226167889684069 14451734659167406479315763)
            ·
              refine ⟨21677601988751109718973645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14451734659167406479315763 21677601988751109718973645)
              ·
                refine ⟨8129100745781666144615117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21677601988751109718973645 8129100745781666144615117)
                ·
                  refine ⟨3048412779668124804230669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8129100745781666144615117 3048412779668124804230669)
                  ·
                    refine ⟨1143154792375546801586501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048412779668124804230669 1143154792375546801586501)
                    ·
                      rfl

theorem cell22_3339429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_3339429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339429 prefixEnd_3339429 := by exact prefixLift 3339429
  have htrace : WordTrace (prefixWord ++ tailWord_3339429) baseStart_3339429 baseEnd_3339429 := by
    simpa [prefixWord, tailWord_3339429, baseEnd_3339429] using wordTrace_append hprefix tailTrace_3339429
  have hstable : (prefixWord ++ tailWord_3339429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339429).length < 2 ^ (prefixWord ++ tailWord_3339429).sum := by decide
  have hdescent : baseEnd_3339429 < baseStart_3339429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339480 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 1, 3]
def baseStart_3339480 : Nat := 118140960795 + 3339480 * 2 ^ 59
def prefixEnd_3339480 : Nat := 4983230072969 + 3 ^ 40 * 3339480 * 2
def baseEnd_3339480 : Nat := 1143172250717799668561345

theorem tailTrace_3339480 : CollatzResearch.WordTrace tailWord_3339480 prefixEnd_3339480 1143172250717799668561345 := by
  unfold tailWord_3339480
  simp only [CollatzResearch.WordTrace]
  refine ⟨60900420970820886311099947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81200561294427848414799929 60900420970820886311099947)
  ·
    refine ⟨91350631456231329466649921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60900420970820886311099947 91350631456231329466649921)
    ·
      refine ⟨68512973592173497099987441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91350631456231329466649921 68512973592173497099987441)
      ·
        refine ⟨51384730194130122824990581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68512973592173497099987441 51384730194130122824990581)
        ·
          refine ⟨4817318455699699014842867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51384730194130122824990581 4817318455699699014842867)
          ·
            refine ⟨7225977683549548522264301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817318455699699014842867 7225977683549548522264301)
            ·
              refine ⟨2709741631331080695849113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7225977683549548522264301 2709741631331080695849113)
              ·
                refine ⟨2032306223498310521886835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2709741631331080695849113 2032306223498310521886835)
                ·
                  refine ⟨3048459335247465782830253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032306223498310521886835 3048459335247465782830253)
                  ·
                    refine ⟨1143172250717799668561345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048459335247465782830253 1143172250717799668561345)
                    ·
                      rfl

theorem cell22_3339480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_3339480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339480 prefixEnd_3339480 := by exact prefixLift 3339480
  have htrace : WordTrace (prefixWord ++ tailWord_3339480) baseStart_3339480 baseEnd_3339480 := by
    simpa [prefixWord, tailWord_3339480, baseEnd_3339480] using wordTrace_append hprefix tailTrace_3339480
  have hstable : (prefixWord ++ tailWord_3339480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339480).length < 2 ^ (prefixWord ++ tailWord_3339480).sum := by decide
  have hdescent : baseEnd_3339480 < baseStart_3339480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339493 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 5]
def baseStart_3339493 : Nat := 118140960795 + 3339493 * 2 ^ 59
def prefixEnd_3339493 : Nat := 4983230072969 + 3 ^ 40 * 3339493 * 2
def baseEnd_3339493 : Nat := 381058900294490655995435

theorem tailTrace_3339493 : CollatzResearch.WordTrace tailWord_3339493 prefixEnd_3339493 381058900294490655995435 := by
  unfold tailWord_3339493
  simp only [CollatzResearch.WordTrace]
  refine ⟨121801316090594675842423133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81200877393729783894948755 121801316090594675842423133)
  ·
    refine ⟨45675493533973003440908675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121801316090594675842423133 45675493533973003440908675)
    ·
      refine ⟨68513240300959505161363013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45675493533973003440908675 68513240300959505161363013)
      ·
        refine ⟨12846232556429907217755565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68513240300959505161363013 12846232556429907217755565)
        ·
          refine ⟨4817337208661215206658337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12846232556429907217755565 4817337208661215206658337)
          ·
            refine ⟨3613002906495911404993753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817337208661215206658337 3613002906495911404993753)
            ·
              refine ⟨2709752179871933553745315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613002906495911404993753 2709752179871933553745315)
              ·
                refine ⟨4064628269807900330617973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709752179871933553745315 4064628269807900330617973)
                ·
                  refine ⟨381058900294490655995435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064628269807900330617973 381058900294490655995435)
                  ·
                    rfl

theorem cell22_3339493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_3339493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339493 prefixEnd_3339493 := by exact prefixLift 3339493
  have htrace : WordTrace (prefixWord ++ tailWord_3339493) baseStart_3339493 baseEnd_3339493 := by
    simpa [prefixWord, tailWord_3339493, baseEnd_3339493] using wordTrace_append hprefix tailTrace_3339493
  have hstable : (prefixWord ++ tailWord_3339493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339493).length < 2 ^ (prefixWord ++ tailWord_3339493).sum := by decide
  have hdescent : baseEnd_3339493 < baseStart_3339493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339506 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_3339506 : Nat := 118140960795 + 3339506 * 2 ^ 59
def prefixEnd_3339506 : Nat := 4983230072969 + 3 ^ 40 * 3339506 * 2
def baseEnd_3339506 : Nat := 1143181151049144267411265

theorem tailTrace_3339506 : CollatzResearch.WordTrace tailWord_3339506 prefixEnd_3339506 1143181151049144267411265 := by
  unfold tailWord_3339506
  simp only [CollatzResearch.WordTrace]
  refine ⟨30450447559886894765661593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81201193493031719375097581 30450447559886894765661593)
  ·
    refine ⟨22837835669915171074246195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30450447559886894765661593 22837835669915171074246195)
    ·
      refine ⟨34256753504872756611369293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22837835669915171074246195 34256753504872756611369293)
      ·
        refine ⟨12846282564327283729263485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34256753504872756611369293 12846282564327283729263485)
        ·
          refine ⟨4817355961622731398473807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12846282564327283729263485 4817355961622731398473807)
          ·
            refine ⟨7226033942434097097710711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817355961622731398473807 7226033942434097097710711)
            ·
              refine ⟨10839050913651145646566067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7226033942434097097710711 10839050913651145646566067)
              ·
                refine ⟨16258576370476718469849101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10839050913651145646566067 16258576370476718469849101)
                ·
                  refine ⟨6096966138928769426193413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16258576370476718469849101 6096966138928769426193413)
                  ·
                    refine ⟨1143181151049144267411265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6096966138928769426193413 1143181151049144267411265)
                    ·
                      rfl

theorem cell22_3339506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_3339506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339506 prefixEnd_3339506 := by exact prefixLift 3339506
  have htrace : WordTrace (prefixWord ++ tailWord_3339506) baseStart_3339506 baseEnd_3339506 := by
    simpa [prefixWord, tailWord_3339506, baseEnd_3339506] using wordTrace_append hprefix tailTrace_3339506
  have hstable : (prefixWord ++ tailWord_3339506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339506).length < 2 ^ (prefixWord ++ tailWord_3339506).sum := by decide
  have hdescent : baseEnd_3339506 < baseStart_3339506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339519 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 1, 5]
def baseStart_3339519 : Nat := 118140960795 + 3339519 * 2 ^ 59
def prefixEnd_3339519 : Nat := 4983230072969 + 3 ^ 40 * 3339519 * 2
def baseEnd_3339519 : Nat := 1143185601214816566836225

theorem tailTrace_3339519 : CollatzResearch.WordTrace tailWord_3339519 prefixEnd_3339519 1143185601214816566836225 := by
  unfold tailWord_3339519
  simp only [CollatzResearch.WordTrace]
  refine ⟨121802264388500482282869611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81201509592333654855246407 121802264388500482282869611)
  ·
    refine ⟨182703396582750723424304417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121802264388500482282869611 182703396582750723424304417)
    ·
      refine ⟨137027547437063042568228313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182703396582750723424304417 137027547437063042568228313)
      ·
        refine ⟨102770660577797281926171235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137027547437063042568228313 102770660577797281926171235)
        ·
          refine ⟨154155990866695922889256853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102770660577797281926171235 154155990866695922889256853)
          ·
            refine ⟨7226062071876371385433915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154155990866695922889256853 7226062071876371385433915)
            ·
              refine ⟨10839093107814557078150873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7226062071876371385433915 10839093107814557078150873)
              ·
                refine ⟨8129319830860917808613155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10839093107814557078150873 8129319830860917808613155)
                ·
                  refine ⟨12193979746291376712919733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129319830860917808613155 12193979746291376712919733)
                  ·
                    refine ⟨1143185601214816566836225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12193979746291376712919733 1143185601214816566836225)
                    ·
                      rfl

theorem cell22_3339519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_3339519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339519 prefixEnd_3339519 := by exact prefixLift 3339519
  have htrace : WordTrace (prefixWord ++ tailWord_3339519) baseStart_3339519 baseEnd_3339519 := by
    simpa [prefixWord, tailWord_3339519, baseEnd_3339519] using wordTrace_append hprefix tailTrace_3339519
  have hstable : (prefixWord ++ tailWord_3339519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339519).length < 2 ^ (prefixWord ++ tailWord_3339519).sum := by decide
  have hdescent : baseEnd_3339519 < baseStart_3339519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339532 : List Nat := [2, 2, 1, 2, 2, 13]
def baseStart_3339532 : Nat := 118140960795 + 3339532 * 2 ^ 59
def prefixEnd_3339532 : Nat := 4983230072969 + 3 ^ 40 * 3339532 * 2
def baseEnd_3339532 : Nat := 14113457424450479830385

theorem tailTrace_3339532 : CollatzResearch.WordTrace tailWord_3339532 prefixEnd_3339532 14113457424450479830385 := by
  unfold tailWord_3339532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60901369268726692751546425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81201825691635590335395233 60901369268726692751546425)
  ·
    refine ⟨45676026951545019563659819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60901369268726692751546425 45676026951545019563659819)
    ·
      refine ⟨68514040427317529345489729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45676026951545019563659819 68514040427317529345489729)
      ·
        refine ⟨51385530320488147009117297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68514040427317529345489729 51385530320488147009117297)
        ·
          refine ⟨38539147740366110256837973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51385530320488147009117297 38539147740366110256837973)
          ·
            refine ⟨14113457424450479830385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38539147740366110256837973 14113457424450479830385)
            ·
              rfl

theorem cell22_3339532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 13].length) (baseStart_3339532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339532 prefixEnd_3339532 := by exact prefixLift 3339532
  have htrace : WordTrace (prefixWord ++ tailWord_3339532) baseStart_3339532 baseEnd_3339532 := by
    simpa [prefixWord, tailWord_3339532, baseEnd_3339532] using wordTrace_append hprefix tailTrace_3339532
  have hstable : (prefixWord ++ tailWord_3339532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339532).length < 2 ^ (prefixWord ++ tailWord_3339532).sum := by decide
  have hdescent : baseEnd_3339532 < baseStart_3339532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339547 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_3339547 : Nat := 118140960795 + 3339547 * 2 ^ 59
def prefixEnd_3339547 : Nat := 4983230072969 + 3 ^ 40 * 3339547 * 2
def baseEnd_3339547 : Nat := 1143195186187033827136139

theorem tailTrace_3339547 : CollatzResearch.WordTrace tailWord_3339547 prefixEnd_3339547 1143195186187033827136139 := by
  unfold tailWord_3339547
  simp only [CollatzResearch.WordTrace]
  refine ⟨121803285632399043064888895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81202190421599362043259263 121803285632399043064888895)
  ·
    refine ⟨182704928448598564597333343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121803285632399043064888895 182704928448598564597333343)
    ·
      refine ⟨274057392672897846896000015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182704928448598564597333343 274057392672897846896000015)
      ·
        refine ⟨411086089009346770344000023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274057392672897846896000015 411086089009346770344000023)
        ·
          refine ⟨616629133514020155516000035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411086089009346770344000023 616629133514020155516000035)
          ·
            refine ⟨924943700271030233274000053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616629133514020155516000035 924943700271030233274000053)
            ·
              refine ⟨86713471900409084369437505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 924943700271030233274000053 86713471900409084369437505)
              ·
                refine ⟨65035103925306813277078129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86713471900409084369437505 65035103925306813277078129)
                ·
                  refine ⟨48776327943980109957808597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65035103925306813277078129 48776327943980109957808597)
                  ·
                    refine ⟨1143195186187033827136139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48776327943980109957808597 1143195186187033827136139)
                    ·
                      rfl

theorem cell22_3339547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_3339547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339547 prefixEnd_3339547 := by exact prefixLift 3339547
  have htrace : WordTrace (prefixWord ++ tailWord_3339547) baseStart_3339547 baseEnd_3339547 := by
    simpa [prefixWord, tailWord_3339547, baseEnd_3339547] using wordTrace_append hprefix tailTrace_3339547
  have hstable : (prefixWord ++ tailWord_3339547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339547).length < 2 ^ (prefixWord ++ tailWord_3339547).sum := by decide
  have hdescent : baseEnd_3339547 < baseStart_3339547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339574 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3339574 : Nat := 118140960795 + 3339574 * 2 ^ 59
def prefixEnd_3339574 : Nat := 4983230072969 + 3 ^ 40 * 3339574 * 2
def baseEnd_3339574 : Nat := 1143204428838814756711057

theorem tailTrace_3339574 : CollatzResearch.WordTrace tailWord_3339574 prefixEnd_3339574 1143204428838814756711057 := by
  unfold tailWord_3339574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612766900206326667257611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81202846935534151117414517 7612766900206326667257611)
  ·
    refine ⟨11419150350309490000886417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7612766900206326667257611 11419150350309490000886417)
    ·
      refine ⟨8564362762732117500664813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11419150350309490000886417 8564362762732117500664813)
      ·
        refine ⟨3211636036024544062749305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8564362762732117500664813 3211636036024544062749305)
        ·
          refine ⟨2408727027018408047061979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3211636036024544062749305 2408727027018408047061979)
          ·
            refine ⟨3613090540527612070592969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408727027018408047061979 3613090540527612070592969)
            ·
              refine ⟨2709817905395709052944727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613090540527612070592969 2709817905395709052944727)
              ·
                refine ⟨4064726858093563579417091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709817905395709052944727 4064726858093563579417091)
                ·
                  refine ⟨6097090287140345369125637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064726858093563579417091 6097090287140345369125637)
                  ·
                    refine ⟨1143204428838814756711057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6097090287140345369125637 1143204428838814756711057)
                    ·
                      rfl

theorem cell22_3339574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3339574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339574 prefixEnd_3339574 := by exact prefixLift 3339574
  have htrace : WordTrace (prefixWord ++ tailWord_3339574) baseStart_3339574 baseEnd_3339574 := by
    simpa [prefixWord, tailWord_3339574, baseEnd_3339574] using wordTrace_append hprefix tailTrace_3339574
  have hstable : (prefixWord ++ tailWord_3339574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339574).length < 2 ^ (prefixWord ++ tailWord_3339574).sum := by decide
  have hdescent : baseEnd_3339574 < baseStart_3339574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339598 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3339598 : Nat := 118140960795 + 3339598 * 2 ^ 59
def prefixEnd_3339598 : Nat := 4983230072969 + 3 ^ 40 * 3339598 * 2
def baseEnd_3339598 : Nat := 1143212644529286694110983

theorem tailTrace_3339598 : CollatzResearch.WordTrace tailWord_3339598 prefixEnd_3339598 1143212644529286694110983 := by
  unfold tailWord_3339598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15225643219401784846874431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81203430503476185849996965 15225643219401784846874431)
  ·
    refine ⟨22838464829102677270311647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15225643219401784846874431 22838464829102677270311647)
    ·
      refine ⟨34257697243654015905467471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22838464829102677270311647 34257697243654015905467471)
      ·
        refine ⟨51386545865481023858201207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34257697243654015905467471 51386545865481023858201207)
        ·
          refine ⟨77079818798221535787301811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51386545865481023858201207 77079818798221535787301811)
          ·
            refine ⟨115619728197332303680952717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77079818798221535787301811 115619728197332303680952717)
            ·
              refine ⟨43357398073999613880357269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115619728197332303680952717 43357398073999613880357269)
              ·
                refine ⟨2032378034718731900641747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43357398073999613880357269 2032378034718731900641747)
                ·
                  refine ⟨3048567052078097850962621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032378034718731900641747 3048567052078097850962621)
                  ·
                    refine ⟨1143212644529286694110983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048567052078097850962621 1143212644529286694110983)
                    ·
                      rfl

theorem cell22_3339598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3339598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339598 prefixEnd_3339598 := by exact prefixLift 3339598
  have htrace : WordTrace (prefixWord ++ tailWord_3339598) baseStart_3339598 baseEnd_3339598 := by
    simpa [prefixWord, tailWord_3339598, baseEnd_3339598] using wordTrace_append hprefix tailTrace_3339598
  have hstable : (prefixWord ++ tailWord_3339598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339598).length < 2 ^ (prefixWord ++ tailWord_3339598).sum := by decide
  have hdescent : baseEnd_3339598 < baseStart_3339598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339609 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_3339609 : Nat := 118140960795 + 3339609 * 2 ^ 59
def prefixEnd_3339609 : Nat := 4983230072969 + 3 ^ 40 * 3339609 * 2
def baseEnd_3339609 : Nat := 1143216410054086332085949

theorem tailTrace_3339609 : CollatzResearch.WordTrace tailWord_3339609 prefixEnd_3339609 1143216410054086332085949 := by
  unfold tailWord_3339609
  simp only [CollatzResearch.WordTrace]
  refine ⟨121805546958174427653645881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81203697972116285102430587 121805546958174427653645881)
  ·
    refine ⟨91354160218630820740234411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121805546958174427653645881 91354160218630820740234411)
    ·
      refine ⟨137031240327946231110351617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91354160218630820740234411 137031240327946231110351617)
      ·
        refine ⟨102773430245959673332763713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137031240327946231110351617 102773430245959673332763713)
        ·
          refine ⟨77080072684469754999572785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102773430245959673332763713 77080072684469754999572785)
          ·
            refine ⟨57810054513352316249679589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77080072684469754999572785 57810054513352316249679589)
            ·
              refine ⟨10839385221253559296814923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57810054513352316249679589 10839385221253559296814923)
              ·
                refine ⟨16259077831880338945222385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10839385221253559296814923 16259077831880338945222385)
                ·
                  refine ⟨12194308373910254208916789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16259077831880338945222385 12194308373910254208916789)
                  ·
                    refine ⟨1143216410054086332085949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12194308373910254208916789 1143216410054086332085949)
                    ·
                      rfl

theorem cell22_3339609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_3339609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339609 prefixEnd_3339609 := by exact prefixLift 3339609
  have htrace : WordTrace (prefixWord ++ tailWord_3339609) baseStart_3339609 baseEnd_3339609 := by
    simpa [prefixWord, tailWord_3339609, baseEnd_3339609] using wordTrace_append hprefix tailTrace_3339609
  have hstable : (prefixWord ++ tailWord_3339609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339609).length < 2 ^ (prefixWord ++ tailWord_3339609).sum := by decide
  have hdescent : baseEnd_3339609 < baseStart_3339609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339641 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_3339641 : Nat := 118140960795 + 3339641 * 2 ^ 59
def prefixEnd_3339641 : Nat := 4983230072969 + 3 ^ 40 * 3339641 * 2
def baseEnd_3339641 : Nat := 1143227364308048915285851

theorem tailTrace_3339641 : CollatzResearch.WordTrace tailWord_3339641 prefixEnd_3339641 1143227364308048915285851 := by
  unfold tailWord_3339641
  simp only [CollatzResearch.WordTrace]
  refine ⟨121806714094058497118810777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81204476062705664745873851 121806714094058497118810777)
  ·
    refine ⟨91355035570543872839108083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121806714094058497118810777 91355035570543872839108083)
    ·
      refine ⟨137032553355815809258662125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91355035570543872839108083 137032553355815809258662125)
      ·
        refine ⟨51387207508430928471998297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137032553355815809258662125 51387207508430928471998297)
        ·
          refine ⟨38540405631323196353998723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51387207508430928471998297 38540405631323196353998723)
          ·
            refine ⟨57810608446984794530998085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38540405631323196353998723 57810608446984794530998085)
            ·
              refine ⟨10839489083809648974562141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57810608446984794530998085 10839489083809648974562141)
              ·
                refine ⟨4064808406428618365460803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10839489083809648974562141 4064808406428618365460803)
                ·
                  refine ⟨6097212609642927548191205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064808406428618365460803 6097212609642927548191205)
                  ·
                    refine ⟨1143227364308048915285851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6097212609642927548191205 1143227364308048915285851)
                    ·
                      rfl

theorem cell22_3339641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_3339641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339641 prefixEnd_3339641 := by exact prefixLift 3339641
  have htrace : WordTrace (prefixWord ++ tailWord_3339641) baseStart_3339641 baseEnd_3339641 := by
    simpa [prefixWord, tailWord_3339641, baseEnd_3339641] using wordTrace_append hprefix tailTrace_3339641
  have hstable : (prefixWord ++ tailWord_3339641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339641).length < 2 ^ (prefixWord ++ tailWord_3339641).sum := by decide
  have hdescent : baseEnd_3339641 < baseStart_3339641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339656 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_3339656 : Nat := 118140960795 + 3339656 * 2 ^ 59
def prefixEnd_3339656 : Nat := 4983230072969 + 3 ^ 40 * 3339656 * 2
def baseEnd_3339656 : Nat := 381077499704864625386935

theorem tailTrace_3339656 : CollatzResearch.WordTrace tailWord_3339656 prefixEnd_3339656 381077499704864625386935 := by
  unfold tailWord_3339656
  simp only [CollatzResearch.WordTrace]
  refine ⟨60903630594502077340303411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81204840792669436453737881 60903630594502077340303411)
  ·
    refine ⟨91355445891753116010455117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60903630594502077340303411 91355445891753116010455117)
    ·
      refine ⟨34258292209407418503920669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91355445891753116010455117 34258292209407418503920669)
      ·
        refine ⟨12846859578527781938970251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34258292209407418503920669 12846859578527781938970251)
        ·
          refine ⟨19270289367791672908455377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12846859578527781938970251 19270289367791672908455377)
          ·
            refine ⟨14452717025843754681341533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270289367791672908455377 14452717025843754681341533)
            ·
              refine ⟨5419768884691408005503075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14452717025843754681341533 5419768884691408005503075)
              ·
                refine ⟨8129653327037112008254613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419768884691408005503075 8129653327037112008254613)
                ·
                  refine ⟨381077499704864625386935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8129653327037112008254613 381077499704864625386935)
                  ·
                    rfl

theorem cell22_3339656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_3339656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339656 prefixEnd_3339656 := by exact prefixLift 3339656
  have htrace : WordTrace (prefixWord ++ tailWord_3339656) baseStart_3339656 baseEnd_3339656 := by
    simpa [prefixWord, tailWord_3339656, baseEnd_3339656] using wordTrace_append hprefix tailTrace_3339656
  have hstable : (prefixWord ++ tailWord_3339656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339656).length < 2 ^ (prefixWord ++ tailWord_3339656).sum := by decide
  have hdescent : baseEnd_3339656 < baseStart_3339656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339662 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_3339662 : Nat := 118140960795 + 3339662 * 2 ^ 59
def prefixEnd_3339662 : Nat := 4983230072969 + 3 ^ 40 * 3339662 * 2
def baseEnd_3339662 : Nat := 381078184345737286836929

theorem tailTrace_3339662 : CollatzResearch.WordTrace tailWord_3339662 prefixEnd_3339662 381078184345737286836929 := by
  unfold tailWord_3339662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15225935003372802213165655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81204986684654945136883493 15225935003372802213165655)
  ·
    refine ⟨22838902505059203319748483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15225935003372802213165655 22838902505059203319748483)
    ·
      refine ⟨34258353757588804979622725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22838902505059203319748483 34258353757588804979622725)
      ·
        refine ⟨6423441329547900933679261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34258353757588804979622725 6423441329547900933679261)
        ·
          refine ⟨2408790498580462850129723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6423441329547900933679261 2408790498580462850129723)
          ·
            refine ⟨3613185747870694275194585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408790498580462850129723 3613185747870694275194585)
            ·
              refine ⟨2709889310903020706395939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613185747870694275194585 2709889310903020706395939)
              ·
                refine ⟨4064833966354531059593909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709889310903020706395939 4064833966354531059593909)
                ·
                  refine ⟨381078184345737286836929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064833966354531059593909 381078184345737286836929)
                  ·
                    rfl

theorem cell22_3339662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_3339662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339662 prefixEnd_3339662 := by exact prefixLift 3339662
  have htrace : WordTrace (prefixWord ++ tailWord_3339662) baseStart_3339662 baseEnd_3339662 := by
    simpa [prefixWord, tailWord_3339662, baseEnd_3339662] using wordTrace_append hprefix tailTrace_3339662
  have hstable : (prefixWord ++ tailWord_3339662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339662).length < 2 ^ (prefixWord ++ tailWord_3339662).sum := by decide
  have hdescent : baseEnd_3339662 < baseStart_3339662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339669 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3339669 : Nat := 118140960795 + 3339669 * 2 ^ 59
def prefixEnd_3339669 : Nat := 4983230072969 + 3 ^ 40 * 3339669 * 2
def baseEnd_3339669 : Nat := 1143236949280266175585765

theorem tailTrace_3339669 : CollatzResearch.WordTrace tailWord_3339669 prefixEnd_3339669 1143236949280266175585765 := by
  unfold tailWord_3339669
  simp only [CollatzResearch.WordTrace]
  refine ⟨121807735337957057900830061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81205156891971371933886707 121807735337957057900830061)
  ·
    refine ⟨45677900751733896712811273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121807735337957057900830061 45677900751733896712811273)
    ·
      refine ⟨34258425563800422534608455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45677900751733896712811273 34258425563800422534608455)
      ·
        refine ⟨51387638345700633801912683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34258425563800422534608455 51387638345700633801912683)
        ·
          refine ⟨77081457518550950702869025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51387638345700633801912683 77081457518550950702869025)
          ·
            refine ⟨57811093138913213027151769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77081457518550950702869025 57811093138913213027151769)
            ·
              refine ⟨43358319854184909770363827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57811093138913213027151769 43358319854184909770363827)
              ·
                refine ⟨65037479781277364655545741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43358319854184909770363827 65037479781277364655545741)
                ·
                  refine ⟨24389054917979011745829653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65037479781277364655545741 24389054917979011745829653)
                  ·
                    refine ⟨1143236949280266175585765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24389054917979011745829653 1143236949280266175585765)
                    ·
                      rfl

theorem cell22_3339669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3339669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339669 prefixEnd_3339669 := by exact prefixLift 3339669
  have htrace : WordTrace (prefixWord ++ tailWord_3339669) baseStart_3339669 baseEnd_3339669 := by
    simpa [prefixWord, tailWord_3339669, baseEnd_3339669] using wordTrace_append hprefix tailTrace_3339669
  have hstable : (prefixWord ++ tailWord_3339669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339669).length < 2 ^ (prefixWord ++ tailWord_3339669).sum := by decide
  have hdescent : baseEnd_3339669 < baseStart_3339669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339705 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_3339705 : Nat := 118140960795 + 3339705 * 2 ^ 59
def prefixEnd_3339705 : Nat := 4983230072969 + 3 ^ 40 * 3339705 * 2
def baseEnd_3339705 : Nat := 1143249272815974081685655

theorem tailTrace_3339705 : CollatzResearch.WordTrace tailWord_3339705 prefixEnd_3339705 1143249272815974081685655 := by
  unfold tailWord_3339705
  simp only [CollatzResearch.WordTrace]
  refine ⟨121809048365826636049140569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81206032243884424032760379 121809048365826636049140569)
  ·
    refine ⟨91356786274369977036855427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121809048365826636049140569 91356786274369977036855427)
    ·
      refine ⟨137035179411554965555283141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91356786274369977036855427 137035179411554965555283141)
      ·
        refine ⟨25694096139666556041615589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137035179411554965555283141 25694096139666556041615589)
        ·
          refine ⟨4817643026187479257802923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25694096139666556041615589 4817643026187479257802923)
          ·
            refine ⟨7226464539281218886704385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817643026187479257802923 7226464539281218886704385)
            ·
              refine ⟨5419848404460914165028289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7226464539281218886704385 5419848404460914165028289)
              ·
                refine ⟨4064886303345685623771217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419848404460914165028289 4064886303345685623771217)
                ·
                  refine ⟨3048664727509264217828413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064886303345685623771217 3048664727509264217828413)
                  ·
                    refine ⟨1143249272815974081685655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048664727509264217828413 1143249272815974081685655)
                    ·
                      rfl

theorem cell22_3339705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_3339705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339705 prefixEnd_3339705 := by exact prefixLift 3339705
  have htrace : WordTrace (prefixWord ++ tailWord_3339705) baseStart_3339705 baseEnd_3339705 := by
    simpa [prefixWord, tailWord_3339705, baseEnd_3339705] using wordTrace_append hprefix tailTrace_3339705
  have hstable : (prefixWord ++ tailWord_3339705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339705).length < 2 ^ (prefixWord ++ tailWord_3339705).sum := by decide
  have hdescent : baseEnd_3339705 < baseStart_3339705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339729 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 11]
def baseStart_3339729 : Nat := 118140960795 + 3339729 * 2 ^ 59
def prefixEnd_3339729 : Nat := 4983230072969 + 3 ^ 40 * 3339729 * 2
def baseEnd_3339729 : Nat := 381085829502148673028527

theorem tailTrace_3339729 : CollatzResearch.WordTrace tailWord_3339729 prefixEnd_3339729 381085829502148673028527 := by
  unfold tailWord_3339729
  simp only [CollatzResearch.WordTrace]
  refine ⟨121809923717739688148014241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81206615811826458765342827 121809923717739688148014241)
  ·
    refine ⟨91357442788304766111010681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121809923717739688148014241 91357442788304766111010681)
    ·
      refine ⟨68518082091228574583258011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91357442788304766111010681 68518082091228574583258011)
      ·
        refine ⟨102777123136842861874887017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68518082091228574583258011 102777123136842861874887017)
        ·
          refine ⟨77082842352632146406165263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102777123136842861874887017 77082842352632146406165263)
          ·
            refine ⟨115624263528948219609247895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77082842352632146406165263 115624263528948219609247895)
            ·
              refine ⟨173436395293422329413871843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115624263528948219609247895 173436395293422329413871843)
              ·
                refine ⟨260154592940133494120807765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173436395293422329413871843 260154592940133494120807765)
                ·
                  refine ⟨381085829502148673028527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 260154592940133494120807765 381085829502148673028527)
                  ·
                    rfl

theorem cell22_3339729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_3339729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339729 prefixEnd_3339729 := by exact prefixLift 3339729
  have htrace : WordTrace (prefixWord ++ tailWord_3339729) baseStart_3339729 baseEnd_3339729 := by
    simpa [prefixWord, tailWord_3339729, baseEnd_3339729] using wordTrace_append hprefix tailTrace_3339729
  have hstable : (prefixWord ++ tailWord_3339729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339729).length < 2 ^ (prefixWord ++ tailWord_3339729).sum := by decide
  have hdescent : baseEnd_3339729 < baseStart_3339729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339733 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3339733 : Nat := 118140960795 + 3339733 * 2 ^ 59
def prefixEnd_3339733 : Nat := 4983230072969 + 3 ^ 40 * 3339733 * 2
def baseEnd_3339733 : Nat := 1143258857788191341985569

theorem tailTrace_3339733 : CollatzResearch.WordTrace tailWord_3339733 prefixEnd_3339733 1143258857788191341985569 := by
  unfold tailWord_3339733
  simp only [CollatzResearch.WordTrace]
  refine ⟨121810069609725196831159853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81206713073150131220773235 121810069609725196831159853)
  ·
    refine ⟨45678776103646948811684945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121810069609725196831159853 45678776103646948811684945)
    ·
      refine ⟨34259082077735211608763709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45678776103646948811684945 34259082077735211608763709)
      ·
        refine ⟨12847155779150704353286391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34259082077735211608763709 12847155779150704353286391)
        ·
          refine ⟨19270733668726056529929587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12847155779150704353286391 19270733668726056529929587)
          ·
            refine ⟨28906100503089084794894381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19270733668726056529929587 28906100503089084794894381)
            ·
              refine ⟨10839787688658406798085393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28906100503089084794894381 10839787688658406798085393)
              ·
                refine ⟨8129840766493805098564045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10839787688658406798085393 8129840766493805098564045)
                ·
                  refine ⟨3048690287435176911961517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8129840766493805098564045 3048690287435176911961517)
                  ·
                    refine ⟨1143258857788191341985569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048690287435176911961517 1143258857788191341985569)
                    ·
                      rfl

theorem cell22_3339733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3339733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339733 prefixEnd_3339733 := by exact prefixLift 3339733
  have htrace : WordTrace (prefixWord ++ tailWord_3339733) baseStart_3339733 baseEnd_3339733 := by
    simpa [prefixWord, tailWord_3339733, baseEnd_3339733] using wordTrace_append hprefix tailTrace_3339733
  have hstable : (prefixWord ++ tailWord_3339733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339733).length < 2 ^ (prefixWord ++ tailWord_3339733).sum := by decide
  have hdescent : baseEnd_3339733 < baseStart_3339733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339761 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3339761 : Nat := 118140960795 + 3339761 * 2 ^ 59
def prefixEnd_3339761 : Nat := 4983230072969 + 3 ^ 40 * 3339761 * 2
def baseEnd_3339761 : Nat := 1143268442760408602285483

theorem tailTrace_3339761 : CollatzResearch.WordTrace tailWord_3339761 prefixEnd_3339761 1143268442760408602285483 := by
  unfold tailWord_3339761
  simp only [CollatzResearch.WordTrace]
  refine ⟨121811090853623757613179137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81207393902415838408786091 121811090853623757613179137)
  ·
    refine ⟨91358318140217818209884353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121811090853623757613179137 91358318140217818209884353)
    ·
      refine ⟨68518738605163363657413265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91358318140217818209884353 68518738605163363657413265)
      ·
        refine ⟨51389053953872522743059949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68518738605163363657413265 51389053953872522743059949)
        ·
          refine ⟨19270895232702196028647481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51389053953872522743059949 19270895232702196028647481)
          ·
            refine ⟨14453171424526647021485611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270895232702196028647481 14453171424526647021485611)
            ·
              refine ⟨21679757136789970532228417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14453171424526647021485611 21679757136789970532228417)
              ·
                refine ⟨16259817852592477899171313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21679757136789970532228417 16259817852592477899171313)
                ·
                  refine ⟨12194863389444358424378485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16259817852592477899171313 12194863389444358424378485)
                  ·
                    refine ⟨1143268442760408602285483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12194863389444358424378485 1143268442760408602285483)
                    ·
                      rfl

theorem cell22_3339761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3339761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339761 prefixEnd_3339761 := by exact prefixLift 3339761
  have htrace : WordTrace (prefixWord ++ tailWord_3339761) baseStart_3339761 baseEnd_3339761 := by
    simpa [prefixWord, tailWord_3339761, baseEnd_3339761] using wordTrace_append hprefix tailTrace_3339761
  have hstable : (prefixWord ++ tailWord_3339761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339761).length < 2 ^ (prefixWord ++ tailWord_3339761).sum := by decide
  have hdescent : baseEnd_3339761 < baseStart_3339761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339793 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_3339793 : Nat := 118140960795 + 3339793 * 2 ^ 59
def prefixEnd_3339793 : Nat := 4983230072969 + 3 ^ 40 * 3339793 * 2
def baseEnd_3339793 : Nat := 1143279397014371185485385

theorem tailTrace_3339793 : CollatzResearch.WordTrace tailWord_3339793 prefixEnd_3339793 1143279397014371185485385 := by
  unfold tailWord_3339793
  simp only [CollatzResearch.WordTrace]
  refine ⟨121812257989507827078344033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81208171993005218052229355 121812257989507827078344033)
  ·
    refine ⟨91359193492130870308758025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121812257989507827078344033 91359193492130870308758025)
    ·
      refine ⟨68519395119098152731568519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91359193492130870308758025 68519395119098152731568519)
      ·
        refine ⟨102779092678647229097352779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68519395119098152731568519 102779092678647229097352779)
        ·
          refine ⟨154168639017970843646029169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102779092678647229097352779 154168639017970843646029169)
          ·
            refine ⟨115626479263478132734521877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154168639017970843646029169 115626479263478132734521877)
            ·
              refine ⟨5419991215475537471930713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115626479263478132734521877 5419991215475537471930713)
              ·
                refine ⟨4064993411606653103948035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419991215475537471930713 4064993411606653103948035)
                ·
                  refine ⟨6097490117409979655922053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064993411606653103948035 6097490117409979655922053)
                  ·
                    refine ⟨1143279397014371185485385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6097490117409979655922053 1143279397014371185485385)
                    ·
                      rfl

theorem cell22_3339793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_3339793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339793 prefixEnd_3339793 := by exact prefixLift 3339793
  have htrace : WordTrace (prefixWord ++ tailWord_3339793) baseStart_3339793 baseEnd_3339793 := by
    simpa [prefixWord, tailWord_3339793, baseEnd_3339793] using wordTrace_append hprefix tailTrace_3339793
  have hstable : (prefixWord ++ tailWord_3339793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339793).length < 2 ^ (prefixWord ++ tailWord_3339793).sum := by decide
  have hdescent : baseEnd_3339793 < baseStart_3339793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339866 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_3339866 : Nat := 118140960795 + 3339866 * 2 ^ 59
def prefixEnd_3339866 : Nat := 4983230072969 + 3 ^ 40 * 3339866 * 2
def baseEnd_3339866 : Nat := 1143304386406223328410161

theorem tailTrace_3339866 : CollatzResearch.WordTrace tailWord_3339866 prefixEnd_3339866 1143304386406223328410161 := by
  unfold tailWord_3339866
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453730129560840136437863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81209947012162240363834301 30453730129560840136437863)
  ·
    refine ⟨45680595194341260204656795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30453730129560840136437863 45680595194341260204656795)
    ·
      refine ⟨68520892791511890306985193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45680595194341260204656795 68520892791511890306985193)
      ·
        refine ⟨51390669593633917730238895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68520892791511890306985193 51390669593633917730238895)
        ·
          refine ⟨77086004390450876595358343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51390669593633917730238895 77086004390450876595358343)
          ·
            refine ⟨115629006585676314893037515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77086004390450876595358343 115629006585676314893037515)
            ·
              refine ⟨173443509878514472339556273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115629006585676314893037515 173443509878514472339556273)
              ·
                refine ⟨130082632408885854254667205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173443509878514472339556273 130082632408885854254667205)
                ·
                  refine ⟨24390493576666097672750101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130082632408885854254667205 24390493576666097672750101)
                  ·
                    refine ⟨1143304386406223328410161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24390493576666097672750101 1143304386406223328410161)
                    ·
                      rfl

theorem cell22_3339866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_3339866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339866 prefixEnd_3339866 := by exact prefixLift 3339866
  have htrace : WordTrace (prefixWord ++ tailWord_3339866) baseStart_3339866 baseEnd_3339866 := by
    simpa [prefixWord, tailWord_3339866, baseEnd_3339866] using wordTrace_append hprefix tailTrace_3339866
  have hstable : (prefixWord ++ tailWord_3339866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339866).length < 2 ^ (prefixWord ++ tailWord_3339866).sum := by decide
  have hdescent : baseEnd_3339866 < baseStart_3339866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339881 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 7]
def baseStart_3339881 : Nat := 118140960795 + 3339881 * 2 ^ 59
def prefixEnd_3339881 : Nat := 4983230072969 + 3 ^ 40 * 3339881 * 2
def baseEnd_3339881 : Nat := 381103173737589429761705

theorem tailTrace_3339881 : CollatzResearch.WordTrace tailWord_3339881 prefixEnd_3339881 381103173737589429761705 := by
  unfold tailWord_3339881
  simp only [CollatzResearch.WordTrace]
  refine ⟨121815467613189018107547497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81210311742126012071698331 121815467613189018107547497)
  ·
    refine ⟨91361600709891763580660623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121815467613189018107547497 91361600709891763580660623)
    ·
      refine ⟨137042401064837645370990935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91361600709891763580660623 137042401064837645370990935)
      ·
        refine ⟨205563601597256468056486403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137042401064837645370990935 205563601597256468056486403)
        ·
          refine ⟨308345402395884702084729605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205563601597256468056486403 308345402395884702084729605)
          ·
            refine ⟨57814762949228381640886801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308345402395884702084729605 57814762949228381640886801)
            ·
              refine ⟨43361072211921286230665101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57814762949228381640886801 43361072211921286230665101)
              ·
                refine ⟨16260402079470482336499413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43361072211921286230665101 16260402079470482336499413)
                ·
                  refine ⟨381103173737589429761705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16260402079470482336499413 381103173737589429761705)
                  ·
                    rfl

theorem cell22_3339881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_3339881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339881 prefixEnd_3339881 := by exact prefixLift 3339881
  have htrace : WordTrace (prefixWord ++ tailWord_3339881) baseStart_3339881 baseEnd_3339881 := by
    simpa [prefixWord, tailWord_3339881, baseEnd_3339881] using wordTrace_append hprefix tailTrace_3339881
  have hstable : (prefixWord ++ tailWord_3339881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339881).length < 2 ^ (prefixWord ++ tailWord_3339881).sum := by decide
  have hdescent : baseEnd_3339881 < baseStart_3339881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339932 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 5]
def baseStart_3339932 : Nat := 118140960795 + 3339932 * 2 ^ 59
def prefixEnd_3339932 : Nat := 4983230072969 + 3 ^ 40 * 3339932 * 2
def baseEnd_3339932 : Nat := 381108993185007052086653

theorem tailTrace_3339932 : CollatzResearch.WordTrace tailWord_3339932 prefixEnd_3339932 381108993185007052086653 := by
  unfold tailWord_3339932
  simp only [CollatzResearch.WordTrace]
  refine ⟨60908663868002126908827025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81211551824002835878436033 60908663868002126908827025)
  ·
    refine ⟨45681497901001595181620269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60908663868002126908827025 45681497901001595181620269)
    ·
      refine ⟨17130561712875598193107601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45681497901001595181620269 17130561712875598193107601)
      ·
        refine ⟨12847921284656698644830701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17130561712875598193107601 12847921284656698644830701)
        ·
          refine ⟨4817970481746261991811513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12847921284656698644830701 4817970481746261991811513)
          ·
            refine ⟨3613477861309696493858635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817970481746261991811513 3613477861309696493858635)
            ·
              refine ⟨5420216791964544740787953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613477861309696493858635 5420216791964544740787953)
              ·
                refine ⟨4065162593973408555590965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5420216791964544740787953 4065162593973408555590965)
                ·
                  refine ⟨381108993185007052086653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4065162593973408555590965 381108993185007052086653)
                  ·
                    rfl

theorem cell22_3339932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_3339932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339932 prefixEnd_3339932 := by exact prefixLift 3339932
  have htrace : WordTrace (prefixWord ++ tailWord_3339932) baseStart_3339932 baseEnd_3339932 := by
    simpa [prefixWord, tailWord_3339932, baseEnd_3339932] using wordTrace_append hprefix tailTrace_3339932
  have hstable : (prefixWord ++ tailWord_3339932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339932).length < 2 ^ (prefixWord ++ tailWord_3339932).sum := by decide
  have hdescent : baseEnd_3339932 < baseStart_3339932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339970 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3339970 : Nat := 118140960795 + 3339970 * 2 ^ 59
def prefixEnd_3339970 : Nat := 4983230072969 + 3 ^ 40 * 3339970 * 2
def baseEnd_3339970 : Nat := 1143339987731601723809843

theorem tailTrace_3339970 : CollatzResearch.WordTrace tailWord_3339970 prefixEnd_3339970 1143339987731601723809843 := by
  unfold tailWord_3339970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30454678427466646576884341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81212475806577724205024909 30454678427466646576884341)
  ·
    refine ⟨2855126102574998116582907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30454678427466646576884341 2855126102574998116582907)
    ·
      refine ⟨4282689153862497174874361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855126102574998116582907 4282689153862497174874361)
      ·
        refine ⟨3212016865396872881155771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4282689153862497174874361 3212016865396872881155771)
        ·
          refine ⟨4818025298095309321733657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212016865396872881155771 4818025298095309321733657)
          ·
            refine ⟨3613518973571481991300243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4818025298095309321733657 3613518973571481991300243)
            ·
              refine ⟨5420278460357222986950365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613518973571481991300243 5420278460357222986950365)
              ·
                refine ⟨2032604422633958620106387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5420278460357222986950365 2032604422633958620106387)
                ·
                  refine ⟨3048906633950937930159581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032604422633958620106387 3048906633950937930159581)
                  ·
                    refine ⟨1143339987731601723809843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048906633950937930159581 1143339987731601723809843)
                    ·
                      rfl

theorem cell22_3339970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3339970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3339970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3339970 prefixEnd_3339970 := by exact prefixLift 3339970
  have htrace : WordTrace (prefixWord ++ tailWord_3339970) baseStart_3339970 baseEnd_3339970 := by
    simpa [prefixWord, tailWord_3339970, baseEnd_3339970] using wordTrace_append hprefix tailTrace_3339970
  have hstable : (prefixWord ++ tailWord_3339970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339970).length < 2 ^ (prefixWord ++ tailWord_3339970).sum := by decide
  have hdescent : baseEnd_3339970 < baseStart_3339970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340033 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 9]
def baseStart_3340033 : Nat := 118140960795 + 3340033 * 2 ^ 59
def prefixEnd_3340033 : Nat := 4983230072969 + 3 ^ 40 * 3340033 * 2
def baseEnd_3340033 : Nat := 381120517973030186494883

theorem tailTrace_3340033 : CollatzResearch.WordTrace tailWord_3340033 prefixEnd_3340033 381120517973030186494883 := by
  unfold tailWord_3340033
  simp only [CollatzResearch.WordTrace]
  refine ⟨121821011508638348067080753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81214007672425565378053835 121821011508638348067080753)
  ·
    refine ⟨91365758631478761050310565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121821011508638348067080753 91365758631478761050310565)
    ·
      refine ⟨17131079743402267696933231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91365758631478761050310565 17131079743402267696933231)
      ·
        refine ⟨25696619615103401545399847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17131079743402267696933231 25696619615103401545399847)
        ·
          refine ⟨38544929422655102318099771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25696619615103401545399847 38544929422655102318099771)
          ·
            refine ⟨57817394133982653477149657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38544929422655102318099771 57817394133982653477149657)
            ·
              refine ⟨43363045600486990107862243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57817394133982653477149657 43363045600486990107862243)
              ·
                refine ⟨65044568400730485161793365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43363045600486990107862243 65044568400730485161793365)
                ·
                  refine ⟨381120517973030186494883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65044568400730485161793365 381120517973030186494883)
                  ·
                    rfl

theorem cell22_3340033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_3340033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340033 prefixEnd_3340033 := by exact prefixLift 3340033
  have htrace : WordTrace (prefixWord ++ tailWord_3340033) baseStart_3340033 baseEnd_3340033 := by
    simpa [prefixWord, tailWord_3340033, baseEnd_3340033] using wordTrace_append hprefix tailTrace_3340033
  have hstable : (prefixWord ++ tailWord_3340033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340033).length < 2 ^ (prefixWord ++ tailWord_3340033).sum := by decide
  have hdescent : baseEnd_3340033 < baseStart_3340033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340065 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3340065 : Nat := 118140960795 + 3340065 * 2 ^ 59
def prefixEnd_3340065 : Nat := 4983230072969 + 3 ^ 40 * 3340065 * 2
def baseEnd_3340065 : Nat := 1143372508173053142684551

theorem tailTrace_3340065 : CollatzResearch.WordTrace tailWord_3340065 prefixEnd_3340065 1143372508173053142684551 := by
  unfold tailWord_3340065
  simp only [CollatzResearch.WordTrace]
  refine ⟨121822178644522417532245649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81214785763014945021497099 121822178644522417532245649)
  ·
    refine ⟨91366633983391813149184237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121822178644522417532245649 91366633983391813149184237)
    ·
      refine ⟨34262487743771929930944089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91366633983391813149184237 34262487743771929930944089)
      ·
        refine ⟨25696865807828947448208067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34262487743771929930944089 25696865807828947448208067)
        ·
          refine ⟨38545298711743421172312101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25696865807828947448208067 38545298711743421172312101)
          ·
            refine ⟨7227243508451891469808519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38545298711743421172312101 7227243508451891469808519)
            ·
              refine ⟨10840865262677837204712779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227243508451891469808519 10840865262677837204712779)
              ·
                refine ⟨16261297894016755807069169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10840865262677837204712779 16261297894016755807069169)
                ·
                  refine ⟨12195973420512566855301877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16261297894016755807069169 12195973420512566855301877)
                  ·
                    refine ⟨1143372508173053142684551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12195973420512566855301877 1143372508173053142684551)
                    ·
                      rfl

theorem cell22_3340065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3340065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340065 prefixEnd_3340065 := by exact prefixLift 3340065
  have htrace : WordTrace (prefixWord ++ tailWord_3340065) baseStart_3340065 baseEnd_3340065 := by
    simpa [prefixWord, tailWord_3340065, baseEnd_3340065] using wordTrace_append hprefix tailTrace_3340065
  have hstable : (prefixWord ++ tailWord_3340065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340065).length < 2 ^ (prefixWord ++ tailWord_3340065).sum := by decide
  have hdescent : baseEnd_3340065 < baseStart_3340065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340127 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 1, 5]
def baseStart_3340127 : Nat := 118140960795 + 3340127 * 2 ^ 59
def prefixEnd_3340127 : Nat := 4983230072969 + 3 ^ 40 * 3340127 * 2
def baseEnd_3340127 : Nat := 1143393732040105647634361

theorem tailTrace_3340127 : CollatzResearch.WordTrace tailWord_3340127 prefixEnd_3340127 1143393732040105647634361 := by
  unfold tailWord_3340127
  simp only [CollatzResearch.WordTrace]
  refine ⟨121824439970297802121002635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81216293313531868080668423 121824439970297802121002635)
  ·
    refine ⟨182736659955446703181503953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121824439970297802121002635 182736659955446703181503953)
    ·
      refine ⟨137052494966585027386127965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182736659955446703181503953 137052494966585027386127965)
      ·
        refine ⟨51394685612469385269797987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137052494966585027386127965 51394685612469385269797987)
        ·
          refine ⟨77092028418704077904696981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51394685612469385269797987 77092028418704077904696981)
          ·
            refine ⟨3613688832126753651782671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77092028418704077904696981 3613688832126753651782671)
            ·
              refine ⟨5420533248190130477674007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613688832126753651782671 5420533248190130477674007)
              ·
                refine ⟨8130799872285195716511011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420533248190130477674007 8130799872285195716511011)
                ·
                  refine ⟨12196199808427793574766517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8130799872285195716511011 12196199808427793574766517)
                  ·
                    refine ⟨1143393732040105647634361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12196199808427793574766517 1143393732040105647634361)
                    ·
                      rfl

theorem cell22_3340127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_3340127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340127 prefixEnd_3340127 := by exact prefixLift 3340127
  have htrace : WordTrace (prefixWord ++ tailWord_3340127) baseStart_3340127 baseEnd_3340127 := by
    simpa [prefixWord, tailWord_3340127, baseEnd_3340127] using wordTrace_append hprefix tailTrace_3340127
  have hstable : (prefixWord ++ tailWord_3340127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340127).length < 2 ^ (prefixWord ++ tailWord_3340127).sum := by decide
  have hdescent : baseEnd_3340127 < baseStart_3340127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340140 : List Nat := [2, 2, 1, 1, 4, 3, 1, 8]
def baseStart_3340140 : Nat := 118140960795 + 3340140 * 2 ^ 59
def prefixEnd_3340140 : Nat := 4983230072969 + 3 ^ 40 * 3340140 * 2
def baseEnd_3340140 : Nat := 127044242467308660784369

theorem tailTrace_3340140 : CollatzResearch.WordTrace tailWord_3340140 prefixEnd_3340140 127044242467308660784369 := by
  unfold tailWord_3340140
  simp only [CollatzResearch.WordTrace]
  refine ⟨60912457059625352670612937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81216609412833803560817249 60912457059625352670612937)
  ·
    refine ⟨45684342794719014502959703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60912457059625352670612937 45684342794719014502959703)
    ·
      refine ⟨68526514192078521754439555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45684342794719014502959703 68526514192078521754439555)
      ·
        refine ⟨102789771288117782631659333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68526514192078521754439555 102789771288117782631659333)
        ·
          refine ⟨19273082116522084243436125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102789771288117782631659333 19273082116522084243436125)
          ·
            refine ⟨7227405793695781591288547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19273082116522084243436125 7227405793695781591288547)
            ·
              refine ⟨10841108690543672386932821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227405793695781591288547 10841108690543672386932821)
              ·
                refine ⟨127044242467308660784369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10841108690543672386932821 127044242467308660784369)
                ·
                  rfl

theorem cell22_3340140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_3340140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340140 prefixEnd_3340140 := by exact prefixLift 3340140
  have htrace : WordTrace (prefixWord ++ tailWord_3340140) baseStart_3340140 baseEnd_3340140 := by
    simpa [prefixWord, tailWord_3340140, baseEnd_3340140] using wordTrace_append hprefix tailTrace_3340140
  have hstable : (prefixWord ++ tailWord_3340140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340140).length < 2 ^ (prefixWord ++ tailWord_3340140).sum := by decide
  have hdescent : baseEnd_3340140 < baseStart_3340140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340142 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3340142 : Nat := 118140960795 + 3340142 * 2 ^ 59
def prefixEnd_3340142 : Nat := 4983230072969 + 3 ^ 40 * 3340142 * 2
def baseEnd_3340142 : Nat := 1143398866846650608509315

theorem tailTrace_3340142 : CollatzResearch.WordTrace tailWord_3340142 prefixEnd_3340142 1143398866846650608509315 := by
  unfold tailWord_3340142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228123383155432460349835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81216658043495639788532453 15228123383155432460349835)
  ·
    refine ⟨22842185074733148690524753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15228123383155432460349835 22842185074733148690524753)
    ·
      refine ⟨17131638806049861517893565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22842185074733148690524753 17131638806049861517893565)
      ·
        refine ⟨6424364552268698069210087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17131638806049861517893565 6424364552268698069210087)
        ·
          refine ⟨9636546828403047103815131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424364552268698069210087 9636546828403047103815131)
          ·
            refine ⟨14454820242604570655722697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9636546828403047103815131 14454820242604570655722697)
            ·
              refine ⟨10841115181953427991792023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14454820242604570655722697 10841115181953427991792023)
              ·
                refine ⟨16261672772930141987688035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10841115181953427991792023 16261672772930141987688035)
                ·
                  refine ⟨24392509159395212981532053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16261672772930141987688035 24392509159395212981532053)
                  ·
                    refine ⟨1143398866846650608509315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24392509159395212981532053 1143398866846650608509315)
                    ·
                      rfl

theorem cell22_3340142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3340142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340142 prefixEnd_3340142 := by exact prefixLift 3340142
  have htrace : WordTrace (prefixWord ++ tailWord_3340142) baseStart_3340142 baseEnd_3340142 := by
    simpa [prefixWord, tailWord_3340142, baseEnd_3340142] using wordTrace_append hprefix tailTrace_3340142
  have hstable : (prefixWord ++ tailWord_3340142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340142).length < 2 ^ (prefixWord ++ tailWord_3340142).sum := by decide
  have hdescent : baseEnd_3340142 < baseStart_3340142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340174 : List Nat := [4, 1, 1, 5, 1, 1, 2, 7]
def baseStart_3340174 : Nat := 118140960795 + 3340174 * 2 ^ 59
def prefixEnd_3340174 : Nat := 4983230072969 + 3 ^ 40 * 3340174 * 2
def baseEnd_3340174 : Nat := 127045535677845910189913

theorem tailTrace_3340174 : CollatzResearch.WordTrace tailWord_3340174 prefixEnd_3340174 127045535677845910189913 := by
  unfold tailWord_3340174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228269275140941143495447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81217436134085019431975717 15228269275140941143495447)
  ·
    refine ⟨22842403912711411715243171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15228269275140941143495447 22842403912711411715243171)
    ·
      refine ⟨34263605869067117572864757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22842403912711411715243171 34263605869067117572864757)
      ·
        refine ⟨3212213050225042272456071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34263605869067117572864757 3212213050225042272456071)
        ·
          refine ⟨4818319575337563408684107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212213050225042272456071 4818319575337563408684107)
          ·
            refine ⟨7227479363006345113026161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818319575337563408684107 7227479363006345113026161)
            ·
              refine ⟨5420609522254758834769621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7227479363006345113026161 5420609522254758834769621)
              ·
                refine ⟨127045535677845910189913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5420609522254758834769621 127045535677845910189913)
                ·
                  rfl

theorem cell22_3340174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_3340174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340174 prefixEnd_3340174 := by exact prefixLift 3340174
  have htrace : WordTrace (prefixWord ++ tailWord_3340174) baseStart_3340174 baseEnd_3340174 := by
    simpa [prefixWord, tailWord_3340174, baseEnd_3340174] using wordTrace_append hprefix tailTrace_3340174
  have hstable : (prefixWord ++ tailWord_3340174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340174).length < 2 ^ (prefixWord ++ tailWord_3340174).sum := by decide
  have hdescent : baseEnd_3340174 < baseStart_3340174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340178 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3340178 : Nat := 118140960795 + 3340178 * 2 ^ 59
def prefixEnd_3340178 : Nat := 4983230072969 + 3 ^ 40 * 3340178 * 2
def baseEnd_3340178 : Nat := 1143411190382358514609205

theorem tailTrace_3340178 : CollatzResearch.WordTrace tailWord_3340178 prefixEnd_3340178 1143411190382358514609205 := by
  unfold tailWord_3340178
  simp only [CollatzResearch.WordTrace]
  refine ⟨30456575023278259457777297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81217533395408691887406125 30456575023278259457777297)
  ·
    refine ⟨22842431267458694593332973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30456575023278259457777297 22842431267458694593332973)
    ·
      refine ⟨8565911725297010472499865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22842431267458694593332973 8565911725297010472499865)
      ·
        refine ⟨6424433793972757854374899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8565911725297010472499865 6424433793972757854374899)
        ·
          refine ⟨9636650690959136781562349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424433793972757854374899 9636650690959136781562349)
          ·
            refine ⟨3613744009109676293085881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9636650690959136781562349 3613744009109676293085881)
            ·
              refine ⟨2710308006832257219814411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613744009109676293085881 2710308006832257219814411)
              ·
                refine ⟨4065462010248385829721617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710308006832257219814411 4065462010248385829721617)
                ·
                  refine ⟨3049096507686289372291213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065462010248385829721617 3049096507686289372291213)
                  ·
                    refine ⟨1143411190382358514609205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049096507686289372291213 1143411190382358514609205)
                    ·
                      rfl

theorem cell22_3340178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3340178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340178 prefixEnd_3340178 := by exact prefixLift 3340178
  have htrace : WordTrace (prefixWord ++ tailWord_3340178) baseStart_3340178 baseEnd_3340178 := by
    simpa [prefixWord, tailWord_3340178, baseEnd_3340178] using wordTrace_append hprefix tailTrace_3340178
  have hstable : (prefixWord ++ tailWord_3340178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340178).length < 2 ^ (prefixWord ++ tailWord_3340178).sum := by decide
  have hdescent : baseEnd_3340178 < baseStart_3340178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340232 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3340232 : Nat := 118140960795 + 3340232 * 2 ^ 59
def prefixEnd_3340232 : Nat := 4983230072969 + 3 ^ 40 * 3340232 * 2
def baseEnd_3340232 : Nat := 1143429675685920373759039

theorem tailTrace_3340232 : CollatzResearch.WordTrace tailWord_3340232 prefixEnd_3340232 1143429675685920373759039 := by
  unfold tailWord_3340232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60914134817458702526787475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81218846423278270035716633 60914134817458702526787475)
  ·
    refine ⟨91371202226188053790181213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60914134817458702526787475 91371202226188053790181213)
    ·
      refine ⟨34264200834820520171317955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91371202226188053790181213 34264200834820520171317955)
      ·
        refine ⟨51396301252230780256976933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34264200834820520171317955 51396301252230780256976933)
        ·
          refine ⟨9636806484793271298183175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51396301252230780256976933 9636806484793271298183175)
          ·
            refine ⟨14455209727189906947274763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9636806484793271298183175 14455209727189906947274763)
            ·
              refine ⟨21682814590784860420912145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14455209727189906947274763 21682814590784860420912145)
              ·
                refine ⟨16262110943088645315684109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21682814590784860420912145 16262110943088645315684109)
                ·
                  refine ⟨6098291603658241993381541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16262110943088645315684109 6098291603658241993381541)
                  ·
                    refine ⟨1143429675685920373759039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098291603658241993381541 1143429675685920373759039)
                    ·
                      rfl

theorem cell22_3340232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3340232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340232 prefixEnd_3340232 := by exact prefixLift 3340232
  have htrace : WordTrace (prefixWord ++ tailWord_3340232) baseStart_3340232 baseEnd_3340232 := by
    simpa [prefixWord, tailWord_3340232, baseEnd_3340232] using wordTrace_append hprefix tailTrace_3340232
  have hstable : (prefixWord ++ tailWord_3340232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340232).length < 2 ^ (prefixWord ++ tailWord_3340232).sum := by decide
  have hdescent : baseEnd_3340232 < baseStart_3340232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340296 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 2, 3]
def baseStart_3340296 : Nat := 118140960795 + 3340296 * 2 ^ 59
def prefixEnd_3340296 : Nat := 4983230072969 + 3 ^ 40 * 3340296 * 2
def baseEnd_3340296 : Nat := 1143451584193845540158843

theorem tailTrace_3340296 : CollatzResearch.WordTrace tailWord_3340296 prefixEnd_3340296 1143451584193845540158843 := by
  unfold tailWord_3340296
  simp only [CollatzResearch.WordTrace]
  refine ⟨60915301953342771991952371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81220402604457029322603161 60915301953342771991952371)
  ·
    refine ⟨91372952930014157987928557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60915301953342771991952371 91372952930014157987928557)
    ·
      refine ⟨34264857348755309245473209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91372952930014157987928557 34264857348755309245473209)
      ·
        refine ⟨25698643011566481934104907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34264857348755309245473209 25698643011566481934104907)
        ·
          refine ⟨38547964517349722901157361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25698643011566481934104907 38547964517349722901157361)
          ·
            refine ⟨28910973388012292175868021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38547964517349722901157361 28910973388012292175868021)
            ·
              refine ⟨2710403755126152391487627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28910973388012292175868021 2710403755126152391487627)
              ·
                refine ⟨4065605632689228587231441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710403755126152391487627 4065605632689228587231441)
                ·
                  refine ⟨3049204224516921440423581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065605632689228587231441 3049204224516921440423581)
                  ·
                    refine ⟨1143451584193845540158843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049204224516921440423581 1143451584193845540158843)
                    ·
                      rfl

theorem cell22_3340296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_3340296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340296 prefixEnd_3340296 := by exact prefixLift 3340296
  have htrace : WordTrace (prefixWord ++ tailWord_3340296) baseStart_3340296 baseEnd_3340296 := by
    simpa [prefixWord, tailWord_3340296, baseEnd_3340296] using wordTrace_append hprefix tailTrace_3340296
  have hstable : (prefixWord ++ tailWord_3340296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340296).length < 2 ^ (prefixWord ++ tailWord_3340296).sum := by decide
  have hdescent : baseEnd_3340296 < baseStart_3340296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340337 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 7]
def baseStart_3340337 : Nat := 118140960795 + 3340337 * 2 ^ 59
def prefixEnd_3340337 : Nat := 4983230072969 + 3 ^ 40 * 3340337 * 2
def baseEnd_3340337 : Nat := 381155206443911699961239

theorem tailTrace_3340337 : CollatzResearch.WordTrace tailWord_3340337 prefixEnd_3340337 381155206443911699961239 := by
  unfold tailWord_3340337
  simp only [CollatzResearch.WordTrace]
  refine ⟨121832099299537007986147265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81221399533024671990764843 121832099299537007986147265)
  ·
    refine ⟨91374074474652755989610449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121832099299537007986147265 91374074474652755989610449)
    ·
      refine ⟨68530555855989566992207837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91374074474652755989610449 68530555855989566992207837)
      ·
        refine ⟨25698958445996087622077939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68530555855989566992207837 25698958445996087622077939)
        ·
          refine ⟨38548437668994131433116909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25698958445996087622077939 38548437668994131433116909)
          ·
            refine ⟨14455664125872799287418841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38548437668994131433116909 14455664125872799287418841)
            ·
              refine ⟨10841748094404599465564131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14455664125872799287418841 10841748094404599465564131)
              ·
                refine ⟨16262622141606899198346197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10841748094404599465564131 16262622141606899198346197)
                ·
                  refine ⟨381155206443911699961239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16262622141606899198346197 381155206443911699961239)
                  ·
                    rfl

theorem cell22_3340337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_3340337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340337 prefixEnd_3340337 := by exact prefixLift 3340337
  have htrace : WordTrace (prefixWord ++ tailWord_3340337) baseStart_3340337 baseEnd_3340337 := by
    simpa [prefixWord, tailWord_3340337, baseEnd_3340337] using wordTrace_append hprefix tailTrace_3340337
  have hstable : (prefixWord ++ tailWord_3340337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340337).length < 2 ^ (prefixWord ++ tailWord_3340337).sum := by decide
  have hdescent : baseEnd_3340337 < baseStart_3340337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340341 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3340341 : Nat := 118140960795 + 3340341 * 2 ^ 59
def prefixEnd_3340341 : Nat := 4983230072969 + 3 ^ 40 * 3340341 * 2
def baseEnd_3340341 : Nat := 1143466988613480422783705

theorem tailTrace_3340341 : CollatzResearch.WordTrace tailWord_3340341 prefixEnd_3340341 1143466988613480422783705 := by
  unfold tailWord_3340341
  simp only [CollatzResearch.WordTrace]
  refine ⟨121832245191522516669292877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81221496794348344446195251 121832245191522516669292877)
  ·
    refine ⟨45687091946820943750984829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121832245191522516669292877 45687091946820943750984829)
    ·
      refine ⟨17132659480057853906619311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45687091946820943750984829 17132659480057853906619311)
      ·
        refine ⟨25698989220086780859928967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17132659480057853906619311 25698989220086780859928967)
        ·
          refine ⟨38548483830130171289893451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25698989220086780859928967 38548483830130171289893451)
          ·
            refine ⟨57822725745195256934840177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38548483830130171289893451 57822725745195256934840177)
            ·
              refine ⟨43367044308896442701130133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57822725745195256934840177 43367044308896442701130133)
              ·
                refine ⟨2032830201979520751615475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43367044308896442701130133 2032830201979520751615475)
                ·
                  refine ⟨3049245302969281127423213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032830201979520751615475 3049245302969281127423213)
                  ·
                    refine ⟨1143466988613480422783705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049245302969281127423213 1143466988613480422783705)
                    ·
                      rfl

theorem cell22_3340341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3340341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340341 prefixEnd_3340341 := by exact prefixLift 3340341
  have htrace : WordTrace (prefixWord ++ tailWord_3340341) baseStart_3340341 baseEnd_3340341 := by
    simpa [prefixWord, tailWord_3340341, baseEnd_3340341] using wordTrace_append hprefix tailTrace_3340341
  have hstable : (prefixWord ++ tailWord_3340341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340341).length < 2 ^ (prefixWord ++ tailWord_3340341).sum := by decide
  have hdescent : baseEnd_3340341 < baseStart_3340341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340367 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 3, 4]
def baseStart_3340367 : Nat := 118140960795 + 3340367 * 2 ^ 59
def prefixEnd_3340367 : Nat := 4983230072969 + 3 ^ 40 * 3340367 * 2
def baseEnd_3340367 : Nat := 1143475888944825021633625

theorem tailTrace_3340367 : CollatzResearch.WordTrace tailWord_3340367 prefixEnd_3340367 1143475888944825021633625 := by
  unfold tailWord_3340367
  simp only [CollatzResearch.WordTrace]
  refine ⟨121833193489428323109739355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81222128992952215406492903 121833193489428323109739355)
  ·
    refine ⟨182749790234142484664609033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121833193489428323109739355 182749790234142484664609033)
    ·
      refine ⟨137062342675606863498456775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182749790234142484664609033 137062342675606863498456775)
      ·
        refine ⟨205593514013410295247685163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137062342675606863498456775 205593514013410295247685163)
        ·
          refine ⟨308390271020115442871527745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205593514013410295247685163 308390271020115442871527745)
          ·
            refine ⟨231292703265086582153645809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308390271020115442871527745 231292703265086582153645809)
            ·
              refine ⟨173469527448814936615234357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231292703265086582153645809 173469527448814936615234357)
              ·
                refine ⟨16262768198326400307678221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173469527448814936615234357 16262768198326400307678221)
                ·
                  refine ⟨6098538074372400115379333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16262768198326400307678221 6098538074372400115379333)
                  ·
                    refine ⟨1143475888944825021633625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098538074372400115379333 1143475888944825021633625)
                    ·
                      rfl

theorem cell22_3340367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_3340367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340367 prefixEnd_3340367 := by exact prefixLift 3340367
  have htrace : WordTrace (prefixWord ++ tailWord_3340367) baseStart_3340367 baseEnd_3340367 := by
    simpa [prefixWord, tailWord_3340367, baseEnd_3340367] using wordTrace_append hprefix tailTrace_3340367
  have hstable : (prefixWord ++ tailWord_3340367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340367).length < 2 ^ (prefixWord ++ tailWord_3340367).sum := by decide
  have hdescent : baseEnd_3340367 < baseStart_3340367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340448 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_3340448 : Nat := 118140960795 + 3340448 * 2 ^ 59
def prefixEnd_3340448 : Nat := 4983230072969 + 3 ^ 40 * 3340448 * 2
def baseEnd_3340448 : Nat := 1143503616900167810358377

theorem tailTrace_3340448 : CollatzResearch.WordTrace tailWord_3340448 prefixEnd_3340448 1143503616900167810358377 := by
  unfold tailWord_3340448
  simp only [CollatzResearch.WordTrace]
  refine ⟨60918073901067436971718999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81224098534756582628958665 60918073901067436971718999)
  ·
    refine ⟨91377110851601155457578499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60918073901067436971718999 91377110851601155457578499)
    ·
      refine ⟨137065666277401733186367749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91377110851601155457578499 137065666277401733186367749)
      ·
        refine ⟨25699812427012824972443953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137065666277401733186367749 25699812427012824972443953)
        ·
          refine ⟨19274859320259618729332965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25699812427012824972443953 19274859320259618729332965)
          ·
            refine ⟨3614036122548678511749931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19274859320259618729332965 3614036122548678511749931)
            ·
              refine ⟨5421054183823017767624897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614036122548678511749931 5421054183823017767624897)
              ·
                refine ⟨4065790637867263325718673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5421054183823017767624897 4065790637867263325718673)
                ·
                  refine ⟨3049342978400447494289005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065790637867263325718673 3049342978400447494289005)
                  ·
                    refine ⟨1143503616900167810358377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049342978400447494289005 1143503616900167810358377)
                    ·
                      rfl

theorem cell22_3340448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_3340448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340448 prefixEnd_3340448 := by exact prefixLift 3340448
  have htrace : WordTrace (prefixWord ++ tailWord_3340448) baseStart_3340448 baseEnd_3340448 := by
    simpa [prefixWord, tailWord_3340448, baseEnd_3340448] using wordTrace_append hprefix tailTrace_3340448
  have hstable : (prefixWord ++ tailWord_3340448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340448).length < 2 ^ (prefixWord ++ tailWord_3340448).sum := by decide
  have hdescent : baseEnd_3340448 < baseStart_3340448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340465 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 2, 3]
def baseStart_3340465 : Nat := 118140960795 + 3340465 * 2 ^ 59
def prefixEnd_3340465 : Nat := 4983230072969 + 3 ^ 40 * 3340465 * 2
def baseEnd_3340465 : Nat := 1143509436347585432683325

theorem tailTrace_3340465 : CollatzResearch.WordTrace tailWord_3340465 prefixEnd_3340465 1143509436347585432683325 := by
  unfold tailWord_3340465
  simp only [CollatzResearch.WordTrace]
  refine ⟨121836767843073285846806849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81224511895382190564537899 121836767843073285846806849)
  ·
    refine ⟨91377575882304964385105137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121836767843073285846806849 91377575882304964385105137)
    ·
      refine ⟨68533181911728723288828853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91377575882304964385105137 68533181911728723288828853)
      ·
        refine ⟨6424985804224567808327705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68533181911728723288828853 6424985804224567808327705)
        ·
          refine ⟨4818739353168425856245779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6424985804224567808327705 4818739353168425856245779)
          ·
            refine ⟨7228109029752638784368669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818739353168425856245779 7228109029752638784368669)
            ·
              refine ⟨2710540886157239544138251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7228109029752638784368669 2710540886157239544138251)
              ·
                refine ⟨4065811329235859316207377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710540886157239544138251 4065811329235859316207377)
                ·
                  refine ⟨3049358496926894487155533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065811329235859316207377 3049358496926894487155533)
                  ·
                    refine ⟨1143509436347585432683325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049358496926894487155533 1143509436347585432683325)
                    ·
                      rfl

theorem cell22_3340465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_3340465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340465 prefixEnd_3340465 := by exact prefixLift 3340465
  have htrace : WordTrace (prefixWord ++ tailWord_3340465) baseStart_3340465 baseEnd_3340465 := by
    simpa [prefixWord, tailWord_3340465, baseEnd_3340465] using wordTrace_append hprefix tailTrace_3340465
  have hstable : (prefixWord ++ tailWord_3340465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340465).length < 2 ^ (prefixWord ++ tailWord_3340465).sum := by decide
  have hdescent : baseEnd_3340465 < baseStart_3340465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340478 : List Nat := [4, 2, 1, 1, 4, 2, 2, 6]
def baseStart_3340478 : Nat := 118140960795 + 3340478 * 2 ^ 59
def prefixEnd_3340478 : Nat := 4983230072969 + 3 ^ 40 * 3340478 * 2
def baseEnd_3340478 : Nat := 127057098501473081345365

theorem tailTrace_3340478 : CollatzResearch.WordTrace tailWord_3340478 prefixEnd_3340478 127057098501473081345365 := by
  unfold tailWord_3340478
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229655249003273633378761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81224827994684126044686725 15229655249003273633378761)
  ·
    refine ⟨11422241436752455225034071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15229655249003273633378761 11422241436752455225034071)
    ·
      refine ⟨17133362155128682837551107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11422241436752455225034071 17133362155128682837551107)
      ·
        refine ⟨25700043232693024256326661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17133362155128682837551107 25700043232693024256326661)
        ·
          refine ⟨4818758106129942048061249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25700043232693024256326661 4818758106129942048061249)
          ·
            refine ⟨3614068579597456536045937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4818758106129942048061249 3614068579597456536045937)
            ·
              refine ⟨2710551434698092402034453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3614068579597456536045937 2710551434698092402034453)
              ·
                refine ⟨127057098501473081345365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2710551434698092402034453 127057098501473081345365)
                ·
                  rfl

theorem cell22_3340478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_3340478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340478 prefixEnd_3340478 := by exact prefixLift 3340478
  have htrace : WordTrace (prefixWord ++ tailWord_3340478) baseStart_3340478 baseEnd_3340478 := by
    simpa [prefixWord, tailWord_3340478, baseEnd_3340478] using wordTrace_append hprefix tailTrace_3340478
  have hstable : (prefixWord ++ tailWord_3340478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340478).length < 2 ^ (prefixWord ++ tailWord_3340478).sum := by decide
  have hdescent : baseEnd_3340478 < baseStart_3340478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340553 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 1, 4]
def baseStart_3340553 : Nat := 118140960795 + 3340553 * 2 ^ 59
def prefixEnd_3340553 : Nat := 4983230072969 + 3 ^ 40 * 3340553 * 2
def baseEnd_3340553 : Nat := 1143539560545982536483055

theorem tailTrace_3340553 : CollatzResearch.WordTrace tailWord_3340553 prefixEnd_3340553 1143539560545982536483055 := by
  unfold tailWord_3340553
  simp only [CollatzResearch.WordTrace]
  refine ⟨121839977466754476876010313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81226651644502984584006875 121839977466754476876010313)
  ·
    refine ⟨91379983100065857657007735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121839977466754476876010313 91379983100065857657007735)
    ·
      refine ⟨137069974650098786485511603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91379983100065857657007735 137069974650098786485511603)
      ·
        refine ⟨205604961975148179728267405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137069974650098786485511603 205604961975148179728267405)
        ·
          refine ⟨77101860740680567398100277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205604961975148179728267405 77101860740680567398100277)
          ·
            refine ⟨7228299444438803193571901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77101860740680567398100277 7228299444438803193571901)
            ·
              refine ⟨2710612291664551197589463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7228299444438803193571901 2710612291664551197589463)
              ·
                refine ⟨4065918437496826796384195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710612291664551197589463 4065918437496826796384195)
                ·
                  refine ⟨6098877656245240194576293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065918437496826796384195 6098877656245240194576293)
                  ·
                    refine ⟨1143539560545982536483055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098877656245240194576293 1143539560545982536483055)
                    ·
                      rfl

theorem cell22_3340553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_3340553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340553 prefixEnd_3340553 := by exact prefixLift 3340553
  have htrace : WordTrace (prefixWord ++ tailWord_3340553) baseStart_3340553 baseEnd_3340553 := by
    simpa [prefixWord, tailWord_3340553, baseEnd_3340553] using wordTrace_append hprefix tailTrace_3340553
  have hstable : (prefixWord ++ tailWord_3340553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340553).length < 2 ^ (prefixWord ++ tailWord_3340553).sum := by decide
  have hdescent : baseEnd_3340553 < baseStart_3340553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340628 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3340628 : Nat := 118140960795 + 3340628 * 2 ^ 59
def prefixEnd_3340628 : Nat := 4983230072969 + 3 ^ 40 * 3340628 * 2
def baseEnd_3340628 : Nat := 1143565234578707340857825

theorem tailTrace_3340628 : CollatzResearch.WordTrace tailWord_3340628 prefixEnd_3340628 1143565234578707340857825 := by
  unfold tailWord_3340628
  simp only [CollatzResearch.WordTrace]
  refine ⟨60921356470741382342495269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81228475294321843123327025 60921356470741382342495269)
  ·
    refine ⟨11422754338264009189217863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60921356470741382342495269 11422754338264009189217863)
    ·
      refine ⟨17134131507396013783826795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11422754338264009189217863 17134131507396013783826795)
      ·
        refine ⟨25701197261094020675740193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17134131507396013783826795 25701197261094020675740193)
        ·
          refine ⟨19275897945820515506805145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25701197261094020675740193 19275897945820515506805145)
          ·
            refine ⟨14456923459365386630103859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19275897945820515506805145 14456923459365386630103859)
            ·
              refine ⟨21685385189048079945155789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14456923459365386630103859 21685385189048079945155789)
              ·
                refine ⟨8132019445893029979433421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21685385189048079945155789 8132019445893029979433421)
                ·
                  refine ⟨3049507292209886242287533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8132019445893029979433421 3049507292209886242287533)
                  ·
                    refine ⟨1143565234578707340857825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049507292209886242287533 1143565234578707340857825)
                    ·
                      rfl

theorem cell22_3340628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3340628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340628 prefixEnd_3340628 := by exact prefixLift 3340628
  have htrace : WordTrace (prefixWord ++ tailWord_3340628) baseStart_3340628 baseEnd_3340628 := by
    simpa [prefixWord, tailWord_3340628, baseEnd_3340628] using wordTrace_append hprefix tailTrace_3340628
  have hstable : (prefixWord ++ tailWord_3340628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340628).length < 2 ^ (prefixWord ++ tailWord_3340628).sum := by decide
  have hdescent : baseEnd_3340628 < baseStart_3340628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340692 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3340692 : Nat := 118140960795 + 3340692 * 2 ^ 59
def prefixEnd_3340692 : Nat := 4983230072969 + 3 ^ 40 * 3340692 * 2
def baseEnd_3340692 : Nat := 381195714362210835752543

theorem tailTrace_3340692 : CollatzResearch.WordTrace tailWord_3340692 prefixEnd_3340692 381195714362210835752543 := by
  unfold tailWord_3340692
  simp only [CollatzResearch.WordTrace]
  refine ⟨60922523606625451807660165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81230031475500602410213553 60922523606625451807660165)
  ·
    refine ⟨11422973176242272213936281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60922523606625451807660165 11422973176242272213936281)
    ·
      refine ⟨8567229882181704160452211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11422973176242272213936281 8567229882181704160452211)
      ·
        refine ⟨12850844823272556240678317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8567229882181704160452211 12850844823272556240678317)
        ·
          refine ⟨4819066808727208590254369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12850844823272556240678317 4819066808727208590254369)
          ·
            refine ⟨3614300106545406442690777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4819066808727208590254369 3614300106545406442690777)
            ·
              refine ⟨2710725079909054832018083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3614300106545406442690777 2710725079909054832018083)
              ·
                refine ⟨4066087619863582248027125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710725079909054832018083 4066087619863582248027125)
                ·
                  refine ⟨381195714362210835752543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4066087619863582248027125 381195714362210835752543)
                  ·
                    rfl

theorem cell22_3340692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3340692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340692 prefixEnd_3340692 := by exact prefixLift 3340692
  have htrace : WordTrace (prefixWord ++ tailWord_3340692) baseStart_3340692 baseEnd_3340692 := by
    simpa [prefixWord, tailWord_3340692, baseEnd_3340692] using wordTrace_append hprefix tailTrace_3340692
  have hstable : (prefixWord ++ tailWord_3340692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340692).length < 2 ^ (prefixWord ++ tailWord_3340692).sum := by decide
  have hdescent : baseEnd_3340692 < baseStart_3340692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340705 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3340705 : Nat := 118140960795 + 3340705 * 2 ^ 59
def prefixEnd_3340705 : Nat := 4983230072969 + 3 ^ 40 * 3340705 * 2
def baseEnd_3340705 : Nat := 1143591593252304806682589

theorem tailTrace_3340705 : CollatzResearch.WordTrace tailWord_3340705 prefixEnd_3340705 1143591593252304806682589 := by
  unfold tailWord_3340705
  simp only [CollatzResearch.WordTrace]
  refine ⟨121845521362203806835543569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81230347574802537890362379 121845521362203806835543569)
  ·
    refine ⟨91384141021652855126657677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121845521362203806835543569 91384141021652855126657677)
    ·
      refine ⟨34269052883119820672496629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91384141021652855126657677 34269052883119820672496629)
      ·
        refine ⟨3212723707792483188046559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34269052883119820672496629 3212723707792483188046559)
        ·
          refine ⟨4819085561688724782069839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212723707792483188046559 4819085561688724782069839)
          ·
            refine ⟨7228628342533087173104759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819085561688724782069839 7228628342533087173104759)
            ·
              refine ⟨10842942513799630759657139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7228628342533087173104759 10842942513799630759657139)
              ·
                refine ⟨16264413770699446139485709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10842942513799630759657139 16264413770699446139485709)
                ·
                  refine ⟨6099155164012292302307141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16264413770699446139485709 6099155164012292302307141)
                  ·
                    refine ⟨1143591593252304806682589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099155164012292302307141 1143591593252304806682589)
                    ·
                      rfl

theorem cell22_3340705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3340705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340705 prefixEnd_3340705 := by exact prefixLift 3340705
  have htrace : WordTrace (prefixWord ++ tailWord_3340705) baseStart_3340705 baseEnd_3340705 := by
    simpa [prefixWord, tailWord_3340705, baseEnd_3340705] using wordTrace_append hprefix tailTrace_3340705
  have hstable : (prefixWord ++ tailWord_3340705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340705).length < 2 ^ (prefixWord ++ tailWord_3340705).sum := by decide
  have hdescent : baseEnd_3340705 < baseStart_3340705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340733 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_3340733 : Nat := 118140960795 + 3340733 * 2 ^ 59
def prefixEnd_3340733 : Nat := 4983230072969 + 3 ^ 40 * 3340733 * 2
def baseEnd_3340733 : Nat := 1143601178224522066982503

theorem tailTrace_3340733 : CollatzResearch.WordTrace tailWord_3340733 prefixEnd_3340733 1143601178224522066982503 := by
  unfold tailWord_3340733
  simp only [CollatzResearch.WordTrace]
  refine ⟨121846542606102367617562853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81231028404068245078375235 121846542606102367617562853)
  ·
    refine ⟨22846226738644193928293035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121846542606102367617562853 22846226738644193928293035)
    ·
      refine ⟨34269340107966290892439553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22846226738644193928293035 34269340107966290892439553)
      ·
        refine ⟨25702005080974718169329665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34269340107966290892439553 25702005080974718169329665)
        ·
          refine ⟨19276503810731038626997249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25702005080974718169329665 19276503810731038626997249)
          ·
            refine ⟨14457377858048278970247937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19276503810731038626997249 14457377858048278970247937)
            ·
              refine ⟨10843033393536209227685953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14457377858048278970247937 10843033393536209227685953)
              ·
                refine ⟨8132275045152156920764465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10843033393536209227685953 8132275045152156920764465)
                ·
                  refine ⟨6099206283864117690573349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132275045152156920764465 6099206283864117690573349)
                  ·
                    refine ⟨1143601178224522066982503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099206283864117690573349 1143601178224522066982503)
                    ·
                      rfl

theorem cell22_3340733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_3340733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340733 prefixEnd_3340733 := by exact prefixLift 3340733
  have htrace : WordTrace (prefixWord ++ tailWord_3340733) baseStart_3340733 baseEnd_3340733 := by
    simpa [prefixWord, tailWord_3340733, baseEnd_3340733] using wordTrace_append hprefix tailTrace_3340733
  have hstable : (prefixWord ++ tailWord_3340733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340733).length < 2 ^ (prefixWord ++ tailWord_3340733).sum := by decide
  have hdescent : baseEnd_3340733 < baseStart_3340733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340761 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_3340761 : Nat := 118140960795 + 3340761 * 2 ^ 59
def prefixEnd_3340761 : Nat := 4983230072969 + 3 ^ 40 * 3340761 * 2
def baseEnd_3340761 : Nat := 1143610763196739327282417

theorem tailTrace_3340761 : CollatzResearch.WordTrace tailWord_3340761 prefixEnd_3340761 1143610763196739327282417 := by
  unfold tailWord_3340761
  simp only [CollatzResearch.WordTrace]
  refine ⟨121847563850000928399582137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81231709233333952266388091 121847563850000928399582137)
  ·
    refine ⟨91385672887500696299686603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121847563850000928399582137 91385672887500696299686603)
    ·
      refine ⟨137078509331251044449529905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91385672887500696299686603 137078509331251044449529905)
      ·
        refine ⟨102808881998438283337147429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137078509331251044449529905 102808881998438283337147429)
        ·
          refine ⟨19276665374707178125715143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102808881998438283337147429 19276665374707178125715143)
          ·
            refine ⟨28914998062060767188572715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19276665374707178125715143 28914998062060767188572715)
            ·
              refine ⟨43372497093091150782859073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28914998062060767188572715 43372497093091150782859073)
              ·
                refine ⟨32529372819818363087144305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43372497093091150782859073 32529372819818363087144305)
                ·
                  refine ⟨24397029614863772315358229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32529372819818363087144305 24397029614863772315358229)
                  ·
                    refine ⟨1143610763196739327282417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24397029614863772315358229 1143610763196739327282417)
                    ·
                      rfl

theorem cell22_3340761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_3340761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340761 prefixEnd_3340761 := by exact prefixLift 3340761
  have htrace : WordTrace (prefixWord ++ tailWord_3340761) baseStart_3340761 baseEnd_3340761 := by
    simpa [prefixWord, tailWord_3340761, baseEnd_3340761] using wordTrace_append hprefix tailTrace_3340761
  have hstable : (prefixWord ++ tailWord_3340761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340761).length < 2 ^ (prefixWord ++ tailWord_3340761).sum := by decide
  have hdescent : baseEnd_3340761 < baseStart_3340761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340793 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 5]
def baseStart_3340793 : Nat := 118140960795 + 3340793 * 2 ^ 59
def prefixEnd_3340793 : Nat := 4983230072969 + 3 ^ 40 * 3340793 * 2
def baseEnd_3340793 : Nat := 381207239150233970160773

theorem tailTrace_3340793 : CollatzResearch.WordTrace tailWord_3340793 prefixEnd_3340793 381207239150233970160773 := by
  unfold tailWord_3340793
  simp only [CollatzResearch.WordTrace]
  refine ⟨121848730985884997864747033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81232487323923331909831355 121848730985884997864747033)
  ·
    refine ⟨91386548239413748398560275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121848730985884997864747033 91386548239413748398560275)
    ·
      refine ⟨137079822359120622597840413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91386548239413748398560275 137079822359120622597840413)
      ·
        refine ⟨51404933384670233474190155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137079822359120622597840413 51404933384670233474190155)
        ·
          refine ⟨77107400077005350211285233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51404933384670233474190155 77107400077005350211285233)
          ·
            refine ⟨57830550057754012658463925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77107400077005350211285233 57830550057754012658463925)
            ·
              refine ⟨5421614067914438686730993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57830550057754012658463925 5421614067914438686730993)
              ·
                refine ⟨4066210550935829015048245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5421614067914438686730993 4066210550935829015048245)
                ·
                  refine ⟨381207239150233970160773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4066210550935829015048245 381207239150233970160773)
                  ·
                    rfl

theorem cell22_3340793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_3340793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340793 prefixEnd_3340793 := by exact prefixLift 3340793
  have htrace : WordTrace (prefixWord ++ tailWord_3340793) baseStart_3340793 baseEnd_3340793 := by
    simpa [prefixWord, tailWord_3340793, baseEnd_3340793] using wordTrace_append hprefix tailTrace_3340793
  have hstable : (prefixWord ++ tailWord_3340793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340793).length < 2 ^ (prefixWord ++ tailWord_3340793).sum := by decide
  have hdescent : baseEnd_3340793 < baseStart_3340793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340810 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_3340810 : Nat := 118140960795 + 3340810 * 2 ^ 59
def prefixEnd_3340810 : Nat := 4983230072969 + 3 ^ 40 * 3340810 * 2
def baseEnd_3340810 : Nat := 381209178966039844269089

theorem tailTrace_3340810 : CollatzResearch.WordTrace tailWord_3340810 prefixEnd_3340810 381209178966039844269089 := by
  unfold tailWord_3340810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30462337756705852442028971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81232900684548939845410589 30462337756705852442028971)
  ·
    refine ⟨45693506635058778663043457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30462337756705852442028971 45693506635058778663043457)
    ·
      refine ⟨34270129976294083997282593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45693506635058778663043457 34270129976294083997282593)
      ·
        refine ⟨25702597482220562997961945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34270129976294083997282593 25702597482220562997961945)
        ·
          refine ⟨19276948111665422248471459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25702597482220562997961945 19276948111665422248471459)
          ·
            refine ⟨28915422167498133372707189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19276948111665422248471459 28915422167498133372707189)
            ·
              refine ⟨2710820828202950003691299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28915422167498133372707189 2710820828202950003691299)
              ·
                refine ⟨4066231242304425005536949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710820828202950003691299 4066231242304425005536949)
                ·
                  refine ⟨381209178966039844269089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4066231242304425005536949 381209178966039844269089)
                  ·
                    rfl

theorem cell22_3340810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_3340810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340810 prefixEnd_3340810 := by exact prefixLift 3340810
  have htrace : WordTrace (prefixWord ++ tailWord_3340810) baseStart_3340810 baseEnd_3340810 := by
    simpa [prefixWord, tailWord_3340810, baseEnd_3340810] using wordTrace_append hprefix tailTrace_3340810
  have hstable : (prefixWord ++ tailWord_3340810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340810).length < 2 ^ (prefixWord ++ tailWord_3340810).sum := by decide
  have hdescent : baseEnd_3340810 < baseStart_3340810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340904 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_3340904 : Nat := 118140960795 + 3340904 * 2 ^ 59
def prefixEnd_3340904 : Nat := 4983230072969 + 3 ^ 40 * 3340904 * 2
def baseEnd_3340904 : Nat := 1143659715019134620956979

theorem tailTrace_3340904 : CollatzResearch.WordTrace tailWord_3340904 prefixEnd_3340904 1143659715019134620956979 := by
  unfold tailWord_3340904
  simp only [CollatzResearch.WordTrace]
  refine ⟨60926389744241431911018883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81235186325655242548025177 60926389744241431911018883)
  ·
    refine ⟨91389584616362147866528325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60926389744241431911018883 91389584616362147866528325)
    ·
      refine ⟨17135547115567902724974061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91389584616362147866528325 17135547115567902724974061)
      ·
        refine ⟨6425830168337963521865273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17135547115567902724974061 6425830168337963521865273)
        ·
          refine ⟨4819372626253472641398955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425830168337963521865273 4819372626253472641398955)
          ·
            refine ⟨7229058939380208962098433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819372626253472641398955 7229058939380208962098433)
            ·
              refine ⟨5421794204535156721573825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7229058939380208962098433 5421794204535156721573825)
              ·
                refine ⟨4066345653401367541180369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5421794204535156721573825 4066345653401367541180369)
                ·
                  refine ⟨3049759240051025655885277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4066345653401367541180369 3049759240051025655885277)
                  ·
                    refine ⟨1143659715019134620956979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049759240051025655885277 1143659715019134620956979)
                    ·
                      rfl

theorem cell22_3340904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_3340904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340904 prefixEnd_3340904 := by exact prefixLift 3340904
  have htrace : WordTrace (prefixWord ++ tailWord_3340904) baseStart_3340904 baseEnd_3340904 := by
    simpa [prefixWord, tailWord_3340904, baseEnd_3340904] using wordTrace_append hprefix tailTrace_3340904
  have hstable : (prefixWord ++ tailWord_3340904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340904).length < 2 ^ (prefixWord ++ tailWord_3340904).sum := by decide
  have hdescent : baseEnd_3340904 < baseStart_3340904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340917 : List Nat := [1, 3, 4, 2, 2, 2, 1, 7]
def baseStart_3340917 : Nat := 118140960795 + 3340917 * 2 ^ 59
def prefixEnd_3340917 : Nat := 4983230072969 + 3 ^ 40 * 3340917 * 2
def baseEnd_3340917 : Nat := 127073796131645213375771

theorem tailTrace_3340917 : CollatzResearch.WordTrace tailWord_3340917 prefixEnd_3340917 127073796131645213375771 := by
  unfold tailWord_3340917
  simp only [CollatzResearch.WordTrace]
  refine ⟨121853253637435767042261005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81235502424957178028174003 121853253637435767042261005)
  ·
    refine ⟨45694970114038412640847877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121853253637435767042261005 45694970114038412640847877)
    ·
      refine ⟨8567806896382202370158977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45694970114038412640847877 8567806896382202370158977)
      ·
        refine ⟨6425855172286651777619233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8567806896382202370158977 6425855172286651777619233)
        ·
          refine ⟨4819391379214988833214425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425855172286651777619233 4819391379214988833214425)
          ·
            refine ⟨3614543534411241624910819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4819391379214988833214425 3614543534411241624910819)
            ·
              refine ⟨5421815301616862437366229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614543534411241624910819 5421815301616862437366229)
              ·
                refine ⟨127073796131645213375771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5421815301616862437366229 127073796131645213375771)
                ·
                  rfl

theorem cell22_3340917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 7].length) (baseStart_3340917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340917 prefixEnd_3340917 := by exact prefixLift 3340917
  have htrace : WordTrace (prefixWord ++ tailWord_3340917) baseStart_3340917 baseEnd_3340917 := by
    simpa [prefixWord, tailWord_3340917, baseEnd_3340917] using wordTrace_append hprefix tailTrace_3340917
  have hstable : (prefixWord ++ tailWord_3340917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340917).length < 2 ^ (prefixWord ++ tailWord_3340917).sum := by decide
  have hdescent : baseEnd_3340917 < baseStart_3340917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340932 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_3340932 : Nat := 118140960795 + 3340932 * 2 ^ 59
def prefixEnd_3340932 : Nat := 4983230072969 + 3 ^ 40 * 3340932 * 2
def baseEnd_3340932 : Nat := 1143669299991351881256893

theorem tailTrace_3340932 : CollatzResearch.WordTrace tailWord_3340932 prefixEnd_3340932 1143669299991351881256893 := by
  unfold tailWord_3340932
  simp only [CollatzResearch.WordTrace]
  refine ⟨60926900366190712302028525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81235867154920949736038033 60926900366190712302028525)
  ·
    refine ⟨22847587637321517113260697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60926900366190712302028525 22847587637321517113260697)
    ·
      refine ⟨17135690727991137834945523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22847587637321517113260697 17135690727991137834945523)
      ·
        refine ⟨25703536091986706752418285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17135690727991137834945523 25703536091986706752418285)
        ·
          refine ⟨9638826034495015032156857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25703536091986706752418285 9638826034495015032156857)
          ·
            refine ⟨7229119525871261274117643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9638826034495015032156857 7229119525871261274117643)
            ·
              refine ⟨10843679288806891911176465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229119525871261274117643 10843679288806891911176465)
              ·
                refine ⟨8132759466605168933382349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10843679288806891911176465 8132759466605168933382349)
                ·
                  refine ⟨3049784799976938350018381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8132759466605168933382349 3049784799976938350018381)
                  ·
                    refine ⟨1143669299991351881256893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049784799976938350018381 1143669299991351881256893)
                    ·
                      rfl

theorem cell22_3340932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_3340932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340932 prefixEnd_3340932 := by exact prefixLift 3340932
  have htrace : WordTrace (prefixWord ++ tailWord_3340932) baseStart_3340932 baseEnd_3340932 := by
    simpa [prefixWord, tailWord_3340932, baseEnd_3340932] using wordTrace_append hprefix tailTrace_3340932
  have hstable : (prefixWord ++ tailWord_3340932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340932).length < 2 ^ (prefixWord ++ tailWord_3340932).sum := by decide
  have hdescent : baseEnd_3340932 < baseStart_3340932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340990 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3340990 : Nat := 118140960795 + 3340990 * 2 ^ 59
def prefixEnd_3340990 : Nat := 4983230072969 + 3 ^ 40 * 3340990 * 2
def baseEnd_3340990 : Nat := 381229718192219687768905

theorem tailTrace_3340990 : CollatzResearch.WordTrace tailWord_3340990 prefixEnd_3340990 381229718192219687768905 := by
  unfold tailWord_3340990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231989520771412563708553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81237277444114200339778949 15231989520771412563708553)
  ·
    refine ⟨11423992140578559422781415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15231989520771412563708553 11423992140578559422781415)
    ·
      refine ⟨17135988210867839134172123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11423992140578559422781415 17135988210867839134172123)
      ·
        refine ⟨25703982316301758701258185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17135988210867839134172123 25703982316301758701258185)
        ·
          refine ⟨19277986737226319025943639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25703982316301758701258185 19277986737226319025943639)
          ·
            refine ⟨28916980105839478538915459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19277986737226319025943639 28916980105839478538915459)
            ·
              refine ⟨43375470158759217808373189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28916980105839478538915459 43375470158759217808373189)
              ·
                refine ⟨8132900654767353339069973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43375470158759217808373189 8132900654767353339069973)
                ·
                  refine ⟨381229718192219687768905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8132900654767353339069973 381229718192219687768905)
                  ·
                    rfl

theorem cell22_3340990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3340990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340990 prefixEnd_3340990 := by exact prefixLift 3340990
  have htrace : WordTrace (prefixWord ++ tailWord_3340990) baseStart_3340990 baseEnd_3340990 := by
    simpa [prefixWord, tailWord_3340990, baseEnd_3340990] using wordTrace_append hprefix tailTrace_3340990
  have hstable : (prefixWord ++ tailWord_3340990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340990).length < 2 ^ (prefixWord ++ tailWord_3340990).sum := by decide
  have hdescent : baseEnd_3340990 < baseStart_3340990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340992 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_3340992 : Nat := 118140960795 + 3340992 * 2 ^ 59
def prefixEnd_3340992 : Nat := 4983230072969 + 3 ^ 40 * 3340992 * 2
def baseEnd_3340992 : Nat := 1143689839217531724756709

theorem tailTrace_3340992 : CollatzResearch.WordTrace tailWord_3340992 prefixEnd_3340992 1143689839217531724756709 := by
  unfold tailWord_3340992
  simp only [CollatzResearch.WordTrace]
  refine ⟨60927994556082027425620615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81237326074776036567494153 60927994556082027425620615)
  ·
    refine ⟨91391991834123041138430923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60927994556082027425620615 91391991834123041138430923)
    ·
      refine ⟨137087987751184561707646385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91391991834123041138430923 137087987751184561707646385)
      ·
        refine ⟨102815990813388421280734789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137087987751184561707646385 102815990813388421280734789)
        ·
          refine ⟨19277998277510328990137773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102815990813388421280734789 19277998277510328990137773)
          ·
            refine ⟨7229249354066373371301665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19277998277510328990137773 7229249354066373371301665)
            ·
              refine ⟨5421937015549780028476249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7229249354066373371301665 5421937015549780028476249)
              ·
                refine ⟨4066452761662335021357187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5421937015549780028476249 4066452761662335021357187)
                ·
                  refine ⟨6099679142493502532035781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066452761662335021357187 6099679142493502532035781)
                  ·
                    refine ⟨1143689839217531724756709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099679142493502532035781 1143689839217531724756709)
                    ·
                      rfl

theorem cell22_3340992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_3340992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3340992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3340992 prefixEnd_3340992 := by exact prefixLift 3340992
  have htrace : WordTrace (prefixWord ++ tailWord_3340992) baseStart_3340992 baseEnd_3340992 := by
    simpa [prefixWord, tailWord_3340992, baseEnd_3340992] using wordTrace_append hprefix tailTrace_3340992
  have hstable : (prefixWord ++ tailWord_3340992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340992).length < 2 ^ (prefixWord ++ tailWord_3340992).sum := by decide
  have hdescent : baseEnd_3340992 < baseStart_3340992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341039 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 2, 3]
def baseStart_3341039 : Nat := 118140960795 + 3341039 * 2 ^ 59
def prefixEnd_3341039 : Nat := 4983230072969 + 3 ^ 40 * 3341039 * 2
def baseEnd_3341039 : Nat := 1143705928278039268831565

theorem tailTrace_3341039 : CollatzResearch.WordTrace tailWord_3341039 prefixEnd_3341039 1143705928278039268831565 := by
  unfold tailWord_3341039
  simp only [CollatzResearch.WordTrace]
  refine ⟨121857703342993781878202171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81238468895329187918801447 121857703342993781878202171)
  ·
    refine ⟨182786555014490672817303257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121857703342993781878202171 182786555014490672817303257)
    ·
      refine ⟨137089916260868004612977443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182786555014490672817303257 137089916260868004612977443)
      ·
        refine ⟨205634874391302006919466165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137089916260868004612977443 205634874391302006919466165)
        ·
          refine ⟨19278269474184563148699953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205634874391302006919466165 19278269474184563148699953)
          ·
            refine ⟨14458702105638422361524965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19278269474184563148699953 14458702105638422361524965)
            ·
              refine ⟨2711006644807204192785931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14458702105638422361524965 2711006644807204192785931)
              ·
                refine ⟨4066509967210806289178897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711006644807204192785931 4066509967210806289178897)
                ·
                  refine ⟨3049882475408104716884173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4066509967210806289178897 3049882475408104716884173)
                  ·
                    refine ⟨1143705928278039268831565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049882475408104716884173 1143705928278039268831565)
                    ·
                      rfl

theorem cell22_3341039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_3341039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341039 prefixEnd_3341039 := by exact prefixLift 3341039
  have htrace : WordTrace (prefixWord ++ tailWord_3341039) baseStart_3341039 baseEnd_3341039 := by
    simpa [prefixWord, tailWord_3341039, baseEnd_3341039] using wordTrace_append hprefix tailTrace_3341039
  have hstable : (prefixWord ++ tailWord_3341039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341039).length < 2 ^ (prefixWord ++ tailWord_3341039).sum := by decide
  have hdescent : baseEnd_3341039 < baseStart_3341039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341054 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3341054 : Nat := 118140960795 + 3341054 * 2 ^ 59
def prefixEnd_3341054 : Nat := 4983230072969 + 3 ^ 40 * 3341054 * 2
def baseEnd_3341054 : Nat := 1143711063084584229706519

theorem tailTrace_3341054 : CollatzResearch.WordTrace tailWord_3341054 prefixEnd_3341054 1143711063084584229706519 := by
  unfold tailWord_3341054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232281304742429929999777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81238833625292959626665477 15232281304742429929999777)
  ·
    refine ⟨11424210978556822447499833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15232281304742429929999777 11424210978556822447499833)
    ·
      refine ⟨8568158233917616835624875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11424210978556822447499833 8568158233917616835624875)
      ·
        refine ⟨12852237350876425253437313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568158233917616835624875 12852237350876425253437313)
        ·
          refine ⟨9639178013157318940077985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12852237350876425253437313 9639178013157318940077985)
          ·
            refine ⟨7229383509867989205058489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9639178013157318940077985 7229383509867989205058489)
            ·
              refine ⟨5422037632400991903793867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7229383509867989205058489 5422037632400991903793867)
              ·
                refine ⟨8133056448601487855690801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422037632400991903793867 8133056448601487855690801)
                ·
                  refine ⟨6099792336451115891768101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8133056448601487855690801 6099792336451115891768101)
                  ·
                    refine ⟨1143711063084584229706519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099792336451115891768101 1143711063084584229706519)
                    ·
                      rfl

theorem cell22_3341054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3341054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341054 prefixEnd_3341054 := by exact prefixLift 3341054
  have htrace : WordTrace (prefixWord ++ tailWord_3341054) baseStart_3341054 baseEnd_3341054 := by
    simpa [prefixWord, tailWord_3341054, baseEnd_3341054] using wordTrace_append hprefix tailTrace_3341054
  have hstable : (prefixWord ++ tailWord_3341054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341054).length < 2 ^ (prefixWord ++ tailWord_3341054).sum := by decide
  have hdescent : baseEnd_3341054 < baseStart_3341054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341118 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_3341118 : Nat := 118140960795 + 3341118 * 2 ^ 59
def prefixEnd_3341118 : Nat := 4983230072969 + 3 ^ 40 * 3341118 * 2
def baseEnd_3341118 : Nat := 1143732971592509396106323

theorem tailTrace_3341118 : CollatzResearch.WordTrace tailWord_3341118 prefixEnd_3341118 1143732971592509396106323 := by
  unfold tailWord_3341118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232573088713447296291001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81240389806471718913552005 15232573088713447296291001)
  ·
    refine ⟨11424429816535085472218251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15232573088713447296291001 11424429816535085472218251)
    ·
      refine ⟨17136644724802628208327377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11424429816535085472218251 17136644724802628208327377)
      ·
        refine ⟨12852483543601971156245533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17136644724802628208327377 12852483543601971156245533)
        ·
          refine ⟨4819681328850739183592075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12852483543601971156245533 4819681328850739183592075)
          ·
            refine ⟨7229521993276108775388113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819681328850739183592075 7229521993276108775388113)
            ·
              refine ⟨5422141494957081581541085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7229521993276108775388113 5422141494957081581541085)
              ·
                refine ⟨2033303060608905593077907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5422141494957081581541085 2033303060608905593077907)
                ·
                  refine ⟨3049954590913358389616861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033303060608905593077907 3049954590913358389616861)
                  ·
                    refine ⟨1143732971592509396106323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049954590913358389616861 1143732971592509396106323)
                    ·
                      rfl

theorem cell22_3341118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_3341118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341118 prefixEnd_3341118 := by exact prefixLift 3341118
  have htrace : WordTrace (prefixWord ++ tailWord_3341118) baseStart_3341118 baseEnd_3341118 := by
    simpa [prefixWord, tailWord_3341118, baseEnd_3341118] using wordTrace_append hprefix tailTrace_3341118
  have hstable : (prefixWord ++ tailWord_3341118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341118).length < 2 ^ (prefixWord ++ tailWord_3341118).sum := by decide
  have hdescent : baseEnd_3341118 < baseStart_3341118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341157 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3341157 : Nat := 118140960795 + 3341157 * 2 ^ 59
def prefixEnd_3341157 : Nat := 4983230072969 + 3 ^ 40 * 3341157 * 2
def baseEnd_3341157 : Nat := 1143746322089526294381203

theorem tailTrace_3341157 : CollatzResearch.WordTrace tailWord_3341157 prefixEnd_3341157 1143746322089526294381203 := by
  unfold tailWord_3341157
  simp only [CollatzResearch.WordTrace]
  refine ⟨121862007156566288030997725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81241338104377525353998483 121862007156566288030997725)
  ·
    refine ⟨45698252683712358011624147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121862007156566288030997725 45698252683712358011624147)
    ·
      refine ⟨68547379025568537017436221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45698252683712358011624147 68547379025568537017436221)
      ·
        refine ⟨25705267134588201381538583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68547379025568537017436221 25705267134588201381538583)
        ·
          refine ⟨38557900701882302072307875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25705267134588201381538583 38557900701882302072307875)
          ·
            refine ⟨57836851052823453108461813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38557900701882302072307875 57836851052823453108461813)
            ·
              refine ⟨5422204786202198728918295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57836851052823453108461813 5422204786202198728918295)
              ·
                refine ⟨8133307179303298093377443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422204786202198728918295 8133307179303298093377443)
                ·
                  refine ⟨12199960768954947140066165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133307179303298093377443 12199960768954947140066165)
                  ·
                    refine ⟨1143746322089526294381203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12199960768954947140066165 1143746322089526294381203)
                    ·
                      rfl

theorem cell22_3341157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3341157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341157 prefixEnd_3341157 := by exact prefixLift 3341157
  have htrace : WordTrace (prefixWord ++ tailWord_3341157) baseStart_3341157 baseEnd_3341157 := by
    simpa [prefixWord, tailWord_3341157, baseEnd_3341157] using wordTrace_append hprefix tailTrace_3341157
  have hstable : (prefixWord ++ tailWord_3341157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341157).length < 2 ^ (prefixWord ++ tailWord_3341157).sum := by decide
  have hdescent : baseEnd_3341157 < baseStart_3341157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341238 : List Nat := [5, 1, 4, 1, 2, 9]
def baseStart_3341238 : Nat := 118140960795 + 3341238 * 2 ^ 59
def prefixEnd_3341238 : Nat := 4983230072969 + 3 ^ 40 * 3341238 * 2
def baseEnd_3341238 : Nat := 14120667284504556581555

theorem tailTrace_3341238 : CollatzResearch.WordTrace tailWord_3341238 prefixEnd_3341238 14120667284504556581555 := by
  unfold tailWord_3341238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616560091829552429043523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81243307646181892576464245 7616560091829552429043523)
  ·
    refine ⟨11424840137744328643565285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616560091829552429043523 11424840137744328643565285)
    ·
      refine ⟨2142157525827061620668491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11424840137744328643565285 2142157525827061620668491)
      ·
        refine ⟨3213236288740592431002737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142157525827061620668491 3213236288740592431002737)
        ·
          refine ⟨2409927216555444323252053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213236288740592431002737 2409927216555444323252053)
          ·
            refine ⟨14120667284504556581555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2409927216555444323252053 14120667284504556581555)
            ·
              rfl

theorem cell22_3341238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 9].length) (baseStart_3341238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341238 prefixEnd_3341238 := by exact prefixLift 3341238
  have htrace : WordTrace (prefixWord ++ tailWord_3341238) baseStart_3341238 baseEnd_3341238 := by
    simpa [prefixWord, tailWord_3341238, baseEnd_3341238] using wordTrace_append hprefix tailTrace_3341238
  have hstable : (prefixWord ++ tailWord_3341238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341238).length < 2 ^ (prefixWord ++ tailWord_3341238).sum := by decide
  have hdescent : baseEnd_3341238 < baseStart_3341238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341300 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3341300 : Nat := 118140960795 + 3341300 * 2 ^ 59
def prefixEnd_3341300 : Nat := 4983230072969 + 3 ^ 40 * 3341300 * 2
def baseEnd_3341300 : Nat := 381265091303973862685255

theorem tailTrace_3341300 : CollatzResearch.WordTrace tailWord_3341300 prefixEnd_3341300 381265091303973862685255 := by
  unfold tailWord_3341300
  simp only [CollatzResearch.WordTrace]
  refine ⟨60933611397524111726726677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81244815196698815635635569 60933611397524111726726677)
  ·
    refine ⟨2856263034258942737190313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60933611397524111726726677 2856263034258942737190313)
    ·
      refine ⟨2142197275694207052892735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2856263034258942737190313 2142197275694207052892735)
      ·
        refine ⟨3213295913541310579339103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142197275694207052892735 3213295913541310579339103)
        ·
          refine ⟨4819943870311965869008655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213295913541310579339103 4819943870311965869008655)
          ·
            refine ⟨7229915805467948803512983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819943870311965869008655 7229915805467948803512983)
            ·
              refine ⟨10844873708201923205269475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229915805467948803512983 10844873708201923205269475)
              ·
                refine ⟨16267310562302884807904213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10844873708201923205269475 16267310562302884807904213)
                ·
                  refine ⟨381265091303973862685255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16267310562302884807904213 381265091303973862685255)
                  ·
                    rfl

theorem cell22_3341300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3341300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341300 prefixEnd_3341300 := by exact prefixLift 3341300
  have htrace : WordTrace (prefixWord ++ tailWord_3341300) baseStart_3341300 baseEnd_3341300 := by
    simpa [prefixWord, tailWord_3341300, baseEnd_3341300] using wordTrace_append hprefix tailTrace_3341300
  have hstable : (prefixWord ++ tailWord_3341300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341300).length < 2 ^ (prefixWord ++ tailWord_3341300).sum := by decide
  have hdescent : baseEnd_3341300 < baseStart_3341300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341307 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 4, 4]
def baseStart_3341307 : Nat := 118140960795 + 3341307 * 2 ^ 59
def prefixEnd_3341307 : Nat := 4983230072969 + 3 ^ 40 * 3341307 * 2
def baseEnd_3341307 : Nat := 1143797670154975903130743

theorem tailTrace_3341307 : CollatzResearch.WordTrace tailWord_3341307 prefixEnd_3341307 1143797670154975903130743 := by
  unfold tailWord_3341307
  simp only [CollatzResearch.WordTrace]
  refine ⟨121867478106022863648958175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81244985404015242432638783 121867478106022863648958175)
  ·
    refine ⟨182801217159034295473437263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121867478106022863648958175 182801217159034295473437263)
    ·
      refine ⟨274201825738551443210155895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182801217159034295473437263 274201825738551443210155895)
      ·
        refine ⟨411302738607827164815233843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274201825738551443210155895 411302738607827164815233843)
        ·
          refine ⟨616954107911740747222850765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411302738607827164815233843 616954107911740747222850765)
          ·
            refine ⟨231357790466902780208569037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616954107911740747222850765 231357790466902780208569037)
            ·
              refine ⟨86759171425088542578213389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231357790466902780208569037 86759171425088542578213389)
              ·
                refine ⟨32534689284408203466830021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86759171425088542578213389 32534689284408203466830021)
                ·
                  refine ⟨6100254240826538150030629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32534689284408203466830021 6100254240826538150030629)
                  ·
                    refine ⟨1143797670154975903130743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6100254240826538150030629 1143797670154975903130743)
                    ·
                      rfl

theorem cell22_3341307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_3341307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341307 prefixEnd_3341307 := by exact prefixLift 3341307
  have htrace : WordTrace (prefixWord ++ tailWord_3341307) baseStart_3341307 baseEnd_3341307 := by
    simpa [prefixWord, tailWord_3341307, baseEnd_3341307] using wordTrace_append hprefix tailTrace_3341307
  have hstable : (prefixWord ++ tailWord_3341307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341307).length < 2 ^ (prefixWord ++ tailWord_3341307).sum := by decide
  have hdescent : baseEnd_3341307 < baseStart_3341307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341326 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3341326 : Nat := 118140960795 + 3341326 * 2 ^ 59
def prefixEnd_3341326 : Nat := 4983230072969 + 3 ^ 40 * 3341326 * 2
def baseEnd_3341326 : Nat := 1143804174243266186905685

theorem tailTrace_3341326 : CollatzResearch.WordTrace tailWord_3341326 prefixEnd_3341326 1143804174243266186905685 := by
  unfold tailWord_3341326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233521386619253736737479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81245447395302686595933221 15233521386619253736737479)
  ·
    refine ⟨22850282079928880605106219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233521386619253736737479 22850282079928880605106219)
    ·
      refine ⟨34275423119893320907659329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22850282079928880605106219 34275423119893320907659329)
      ·
        refine ⟨25706567339919990680744497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34275423119893320907659329 25706567339919990680744497)
        ·
          refine ⟨19279925504939993010558373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25706567339919990680744497 19279925504939993010558373)
          ·
            refine ⟨3614986032176248689479695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19279925504939993010558373 3614986032176248689479695)
            ·
              refine ⟨5422479048264373034219543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614986032176248689479695 5422479048264373034219543)
              ·
                refine ⟨8133718572396559551329315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422479048264373034219543 8133718572396559551329315)
                ·
                  refine ⟨12200577858594839326993973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133718572396559551329315 12200577858594839326993973)
                  ·
                    refine ⟨1143804174243266186905685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12200577858594839326993973 1143804174243266186905685)
                    ·
                      rfl

theorem cell22_3341326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3341326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341326 prefixEnd_3341326 := by exact prefixLift 3341326
  have htrace : WordTrace (prefixWord ++ tailWord_3341326) baseStart_3341326 baseEnd_3341326 := by
    simpa [prefixWord, tailWord_3341326, baseEnd_3341326] using wordTrace_append hprefix tailTrace_3341326
  have hstable : (prefixWord ++ tailWord_3341326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341326).length < 2 ^ (prefixWord ++ tailWord_3341326).sum := by decide
  have hdescent : baseEnd_3341326 < baseStart_3341326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341377 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3341377 : Nat := 118140960795 + 3341377 * 2 ^ 59
def prefixEnd_3341377 : Nat := 4983230072969 + 3 ^ 40 * 3341377 * 2
def baseEnd_3341377 : Nat := 1143821632585519053880529

theorem tailTrace_3341377 : CollatzResearch.WordTrace tailWord_3341377 prefixEnd_3341377 1143821632585519053880529 := by
  unfold tailWord_3341377
  simp only [CollatzResearch.WordTrace]
  refine ⟨121870031215769265604006385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81246687477179510402670923 121870031215769265604006385)
  ·
    refine ⟨91402523411826949203004789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121870031215769265604006385 91402523411826949203004789)
    ·
      refine ⟨8568986569858776487781699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91402523411826949203004789 8568986569858776487781699)
      ·
        refine ⟨12853479854788164731672549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568986569858776487781699 12853479854788164731672549)
        ·
          refine ⟨2410027472772780887188603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12853479854788164731672549 2410027472772780887188603)
          ·
            refine ⟨3615041209159171330782905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410027472772780887188603 3615041209159171330782905)
            ·
              refine ⟨2711280906869378498087179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615041209159171330782905 2711280906869378498087179)
              ·
                refine ⟨4066921360304067747130769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711280906869378498087179 4066921360304067747130769)
                ·
                  refine ⟨3050191020228050810348077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4066921360304067747130769 3050191020228050810348077)
                  ·
                    refine ⟨1143821632585519053880529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050191020228050810348077 1143821632585519053880529)
                    ·
                      rfl

theorem cell22_3341377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3341377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341377 prefixEnd_3341377 := by exact prefixLift 3341377
  have htrace : WordTrace (prefixWord ++ tailWord_3341377) baseStart_3341377 baseEnd_3341377 := by
    simpa [prefixWord, tailWord_3341377, baseEnd_3341377] using wordTrace_append hprefix tailTrace_3341377
  have hstable : (prefixWord ++ tailWord_3341377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341377).length < 2 ^ (prefixWord ++ tailWord_3341377).sum := by decide
  have hdescent : baseEnd_3341377 < baseStart_3341377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341384 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_3341384 : Nat := 118140960795 + 3341384 * 2 ^ 59
def prefixEnd_3341384 : Nat := 4983230072969 + 3 ^ 40 * 3341384 * 2
def baseEnd_3341384 : Nat := 381274676276191122985169

theorem tailTrace_3341384 : CollatzResearch.WordTrace tailWord_3341384 prefixEnd_3341384 381274676276191122985169 := by
  unfold tailWord_3341384
  simp only [CollatzResearch.WordTrace]
  refine ⟨60935143263371952899755603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81246857684495937199674137 60935143263371952899755603)
  ·
    refine ⟨91402714895057929349633405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60935143263371952899755603 91402714895057929349633405)
    ·
      refine ⟨34276018085646723506112527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91402714895057929349633405 34276018085646723506112527)
      ·
        refine ⟨51414027128470085259168791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34276018085646723506112527 51414027128470085259168791)
        ·
          refine ⟨77121040692705127888753187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51414027128470085259168791 77121040692705127888753187)
          ·
            refine ⟨115681561039057691833129781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77121040692705127888753187 115681561039057691833129781)
            ·
              refine ⟨10845146347411658609355917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115681561039057691833129781 10845146347411658609355917)
              ·
                refine ⟨4066929880279371978508469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10845146347411658609355917 4066929880279371978508469)
                ·
                  refine ⟨381274676276191122985169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4066929880279371978508469 381274676276191122985169)
                  ·
                    rfl

theorem cell22_3341384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_3341384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341384 prefixEnd_3341384 := by exact prefixLift 3341384
  have htrace : WordTrace (prefixWord ++ tailWord_3341384) baseStart_3341384 baseEnd_3341384 := by
    simpa [prefixWord, tailWord_3341384, baseEnd_3341384] using wordTrace_append hprefix tailTrace_3341384
  have hstable : (prefixWord ++ tailWord_3341384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341384).length < 2 ^ (prefixWord ++ tailWord_3341384).sum := by decide
  have hdescent : baseEnd_3341384 < baseStart_3341384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341422 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3341422 : Nat := 118140960795 + 3341422 * 2 ^ 59
def prefixEnd_3341422 : Nat := 4983230072969 + 3 ^ 40 * 3341422 * 2
def baseEnd_3341422 : Nat := 1143837037005153936505391

theorem tailTrace_3341422 : CollatzResearch.WordTrace tailWord_3341422 prefixEnd_3341422 1143837037005153936505391 := by
  unfold tailWord_3341422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233959062575779786174315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81247781667070825526263013 15233959062575779786174315)
  ·
    refine ⟨22850938593863669679261473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233959062575779786174315 22850938593863669679261473)
    ·
      refine ⟨17138203945397752259446105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22850938593863669679261473 17138203945397752259446105)
      ·
        refine ⟨12853652959048314194584579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17138203945397752259446105 12853652959048314194584579)
        ·
          refine ⟨19280479438572471291876869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12853652959048314194584579 19280479438572471291876869)
          ·
            refine ⟨3615089894732338367226913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19280479438572471291876869 3615089894732338367226913)
            ·
              refine ⟨2711317421049253775420185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615089894732338367226913 2711317421049253775420185)
              ·
                refine ⟨2033488065786940331565139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711317421049253775420185 2033488065786940331565139)
                ·
                  refine ⟨3050232098680410497347709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033488065786940331565139 3050232098680410497347709)
                  ·
                    refine ⟨1143837037005153936505391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050232098680410497347709 1143837037005153936505391)
                    ·
                      rfl

theorem cell22_3341422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3341422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341422 prefixEnd_3341422 := by exact prefixLift 3341422
  have htrace : WordTrace (prefixWord ++ tailWord_3341422) baseStart_3341422 baseEnd_3341422 := by
    simpa [prefixWord, tailWord_3341422, baseEnd_3341422] using wordTrace_append hprefix tailTrace_3341422
  have hstable : (prefixWord ++ tailWord_3341422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341422).length < 2 ^ (prefixWord ++ tailWord_3341422).sum := by decide
  have hdescent : baseEnd_3341422 < baseStart_3341422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341463 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 4]
def baseStart_3341463 : Nat := 118140960795 + 3341463 * 2 ^ 59
def prefixEnd_3341463 : Nat := 4983230072969 + 3 ^ 40 * 3341463 * 2
def baseEnd_3341463 : Nat := 381283690714347832076755

theorem tailTrace_3341463 : CollatzResearch.WordTrace tailWord_3341463 prefixEnd_3341463 381283690714347832076755 := by
  unfold tailWord_3341463
  simp only [CollatzResearch.WordTrace]
  refine ⟨121873167893457702291637043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81248778595638468194424695 121873167893457702291637043)
  ·
    refine ⟨182809751840186553437455565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121873167893457702291637043 182809751840186553437455565)
    ·
      refine ⟨68553656940069957539045837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182809751840186553437455565 68553656940069957539045837)
      ·
        refine ⟨25707621352526234077142189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68553656940069957539045837 25707621352526234077142189)
        ·
          refine ⟨9640358007197337778928321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25707621352526234077142189 9640358007197337778928321)
          ·
            refine ⟨7230268505398003334196241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9640358007197337778928321 7230268505398003334196241)
            ·
              refine ⟨5422701379048502500647181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7230268505398003334196241 5422701379048502500647181)
              ·
                refine ⟨2033513017143188437742693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5422701379048502500647181 2033513017143188437742693)
                ·
                  refine ⟨381283690714347832076755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033513017143188437742693 381283690714347832076755)
                  ·
                    rfl

theorem cell22_3341463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 4].length) (baseStart_3341463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341463 prefixEnd_3341463 := by exact prefixLift 3341463
  have htrace : WordTrace (prefixWord ++ tailWord_3341463) baseStart_3341463 baseEnd_3341463 := by
    simpa [prefixWord, tailWord_3341463, baseEnd_3341463] using wordTrace_append hprefix tailTrace_3341463
  have hstable : (prefixWord ++ tailWord_3341463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341463).length < 2 ^ (prefixWord ++ tailWord_3341463).sum := by decide
  have hdescent : baseEnd_3341463 < baseStart_3341463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341628 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_3341628 : Nat := 118140960795 + 3341628 * 2 ^ 59
def prefixEnd_3341628 : Nat := 4983230072969 + 3 ^ 40 * 3341628 * 2
def baseEnd_3341628 : Nat := 1143907555015038065854759

theorem tailTrace_3341628 : CollatzResearch.WordTrace tailWord_3341628 prefixEnd_3341628 1143907555015038065854759 := by
  unfold tailWord_3341628
  simp only [CollatzResearch.WordTrace]
  refine ⟨60939592968929967735696769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81252790625239956980929025 60939592968929967735696769)
  ·
    refine ⟨45704694726697475801772577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60939592968929967735696769 45704694726697475801772577)
    ·
      refine ⟨34278521045023106851329433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45704694726697475801772577 34278521045023106851329433)
      ·
        refine ⟨25708890783767330138497075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34278521045023106851329433 25708890783767330138497075)
        ·
          refine ⟨38563336175650995207745613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25708890783767330138497075 38563336175650995207745613)
          ·
            refine ⟨14461251065869123202904605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38563336175650995207745613 14461251065869123202904605)
            ·
              refine ⟨5422969149700921201089227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14461251065869123202904605 5422969149700921201089227)
              ·
                refine ⟨8134453724551381801633841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422969149700921201089227 8134453724551381801633841)
                ·
                  refine ⟨6100840293413536351225381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134453724551381801633841 6100840293413536351225381)
                  ·
                    refine ⟨1143907555015038065854759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6100840293413536351225381 1143907555015038065854759)
                    ·
                      rfl

theorem cell22_3341628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_3341628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341628 prefixEnd_3341628 := by exact prefixLift 3341628
  have htrace : WordTrace (prefixWord ++ tailWord_3341628) baseStart_3341628 baseEnd_3341628 := by
    simpa [prefixWord, tailWord_3341628, baseEnd_3341628] using wordTrace_append hprefix tailTrace_3341628
  have hstable : (prefixWord ++ tailWord_3341628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341628).length < 2 ^ (prefixWord ++ tailWord_3341628).sum := by decide
  have hdescent : baseEnd_3341628 < baseStart_3341628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341658 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_3341658 : Nat := 118140960795 + 3341658 * 2 ^ 59
def prefixEnd_3341658 : Nat := 4983230072969 + 3 ^ 40 * 3341658 * 2
def baseEnd_3341658 : Nat := 1143917824628127987604667

theorem tailTrace_3341658 : CollatzResearch.WordTrace tailWord_3341658 prefixEnd_3341658 1143917824628127987604667 := by
  unfold tailWord_3341658
  simp only [CollatzResearch.WordTrace]
  refine ⟨30470070031937812648746407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81253520085167500396657085 30470070031937812648746407)
  ·
    refine ⟨45705105047906718973119611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30470070031937812648746407 45705105047906718973119611)
    ·
      refine ⟨68557657571860078459679417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45705105047906718973119611 68557657571860078459679417)
      ·
        refine ⟨51418243178895058844759563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68557657571860078459679417 51418243178895058844759563)
        ·
          refine ⟨77127364768342588267139345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51418243178895058844759563 77127364768342588267139345)
          ·
            refine ⟨57845523576256941200354509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77127364768342588267139345 57845523576256941200354509)
            ·
              refine ⟨21692071341096352950132941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57845523576256941200354509 21692071341096352950132941)
              ·
                refine ⟨8134526752911132356299853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21692071341096352950132941 8134526752911132356299853)
                ·
                  refine ⟨3050447532341674633612445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8134526752911132356299853 3050447532341674633612445)
                  ·
                    refine ⟨1143917824628127987604667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050447532341674633612445 1143917824628127987604667)
                    ·
                      rfl

theorem cell22_3341658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_3341658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341658 prefixEnd_3341658 := by exact prefixLift 3341658
  have htrace : WordTrace (prefixWord ++ tailWord_3341658) baseStart_3341658 baseEnd_3341658 := by
    simpa [prefixWord, tailWord_3341658, baseEnd_3341658] using wordTrace_append hprefix tailTrace_3341658
  have hstable : (prefixWord ++ tailWord_3341658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341658).length < 2 ^ (prefixWord ++ tailWord_3341658).sum := by decide
  have hdescent : baseEnd_3341658 < baseStart_3341658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341763 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 2, 4]
def baseStart_3341763 : Nat := 118140960795 + 3341763 * 2 ^ 59
def prefixEnd_3341763 : Nat := 4983230072969 + 3 ^ 40 * 3341763 * 2
def baseEnd_3341763 : Nat := 1143953768273942713729345

theorem tailTrace_3341763 : CollatzResearch.WordTrace tailWord_3341763 prefixEnd_3341763 1143953768273942713729345 := by
  unfold tailWord_3341763
  simp only [CollatzResearch.WordTrace]
  refine ⟨121884109792370853527557943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81256073194913902351705295 121884109792370853527557943)
  ·
    refine ⟨182826164688556280291336915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121884109792370853527557943 182826164688556280291336915)
    ·
      refine ⟨274239247032834420437005373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182826164688556280291336915 274239247032834420437005373)
      ·
        refine ⟨102839717637312907663877015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274239247032834420437005373 102839717637312907663877015)
        ·
          refine ⟨154259576455969361495815523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102839717637312907663877015 154259576455969361495815523)
          ·
            refine ⟨231389364683954042243723285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154259576455969361495815523 231389364683954042243723285)
            ·
              refine ⟨10846376469560345730174529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231389364683954042243723285 10846376469560345730174529)
              ·
                refine ⟨8134782352170259297630897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10846376469560345730174529 8134782352170259297630897)
                ·
                  refine ⟨6101086764127694473223173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134782352170259297630897 6101086764127694473223173)
                  ·
                    refine ⟨1143953768273942713729345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6101086764127694473223173 1143953768273942713729345)
                    ·
                      rfl

theorem cell22_3341763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_3341763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341763 prefixEnd_3341763 := by exact prefixLift 3341763
  have htrace : WordTrace (prefixWord ++ tailWord_3341763) baseStart_3341763 baseEnd_3341763 := by
    simpa [prefixWord, tailWord_3341763, baseEnd_3341763] using wordTrace_append hprefix tailTrace_3341763
  have hstable : (prefixWord ++ tailWord_3341763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341763).length < 2 ^ (prefixWord ++ tailWord_3341763).sum := by decide
  have hdescent : baseEnd_3341763 < baseStart_3341763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341782 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3341782 : Nat := 118140960795 + 3341782 * 2 ^ 59
def prefixEnd_3341782 : Nat := 4983230072969 + 3 ^ 40 * 3341782 * 2
def baseEnd_3341782 : Nat := 1143960272362232997504287

theorem tailTrace_3341782 : CollatzResearch.WordTrace tailWord_3341782 prefixEnd_3341782 1143960272362232997504287 := by
  unfold tailWord_3341782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7617800173706376235781225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81256535186201346514999733 7617800173706376235781225)
  ·
    refine ⟨5713350130279782176835919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7617800173706376235781225 5713350130279782176835919)
    ·
      refine ⟨8570025195419673265253879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5713350130279782176835919 8570025195419673265253879)
      ·
        refine ⟨12855037793129509897880819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8570025195419673265253879 12855037793129509897880819)
        ·
          refine ⟨19282556689694264846821229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12855037793129509897880819 19282556689694264846821229)
          ·
            refine ⟨7230958758635349317557961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19282556689694264846821229 7230958758635349317557961)
            ·
              refine ⟨5423219068976511988168471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7230958758635349317557961 5423219068976511988168471)
              ·
                refine ⟨8134828603464767982252707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423219068976511988168471 8134828603464767982252707)
                ·
                  refine ⟨12202242905197151973379061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8134828603464767982252707 12202242905197151973379061)
                  ·
                    refine ⟨1143960272362232997504287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12202242905197151973379061 1143960272362232997504287)
                    ·
                      rfl

theorem cell22_3341782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3341782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341782 prefixEnd_3341782 := by exact prefixLift 3341782
  have htrace : WordTrace (prefixWord ++ tailWord_3341782) baseStart_3341782 baseEnd_3341782 := by
    simpa [prefixWord, tailWord_3341782, baseEnd_3341782] using wordTrace_append hprefix tailTrace_3341782
  have hstable : (prefixWord ++ tailWord_3341782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341782).length < 2 ^ (prefixWord ++ tailWord_3341782).sum := by decide
  have hdescent : baseEnd_3341782 < baseStart_3341782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341795 : List Nat := [1, 1, 1, 6, 2, 2, 3, 6]
def baseStart_3341795 : Nat := 118140960795 + 3341795 * 2 ^ 59
def prefixEnd_3341795 : Nat := 4983230072969 + 3 ^ 40 * 3341795 * 2
def baseEnd_3341795 : Nat := 127107191391989477436583

theorem tailTrace_3341795 : CollatzResearch.WordTrace tailWord_3341795 prefixEnd_3341795 127107191391989477436583 := by
  unfold tailWord_3341795
  simp only [CollatzResearch.WordTrace]
  refine ⟨121885276928254922992722839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81256851285503281995148559 121885276928254922992722839)
  ·
    refine ⟨182827915392382384489084259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121885276928254922992722839 182827915392382384489084259)
    ·
      refine ⟨274241873088573576733626389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182827915392382384489084259 274241873088573576733626389)
      ·
        refine ⟨12855087801026886409388737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 274241873088573576733626389 12855087801026886409388737)
        ·
          refine ⟨9641315850770164807041553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12855087801026886409388737 9641315850770164807041553)
          ·
            refine ⟨7230986888077623605281165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9641315850770164807041553 7230986888077623605281165)
            ·
              refine ⟨2711620083029108851980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7230986888077623605281165 2711620083029108851980437)
              ·
                refine ⟨127107191391989477436583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2711620083029108851980437 127107191391989477436583)
                ·
                  rfl

theorem cell22_3341795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 6].length) (baseStart_3341795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341795 prefixEnd_3341795 := by exact prefixLift 3341795
  have htrace : WordTrace (prefixWord ++ tailWord_3341795) baseStart_3341795 baseEnd_3341795 := by
    simpa [prefixWord, tailWord_3341795, baseEnd_3341795] using wordTrace_append hprefix tailTrace_3341795
  have hstable : (prefixWord ++ tailWord_3341795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341795).length < 2 ^ (prefixWord ++ tailWord_3341795).sum := by decide
  have hdescent : baseEnd_3341795 < baseStart_3341795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341797 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_3341797 : Nat := 118140960795 + 3341797 * 2 ^ 59
def prefixEnd_3341797 : Nat := 4983230072969 + 3 ^ 40 * 3341797 * 2
def baseEnd_3341797 : Nat := 1143965407168777958379241

theorem tailTrace_3341797 : CollatzResearch.WordTrace tailWord_3341797 prefixEnd_3341797 1143965407168777958379241 := by
  unfold tailWord_3341797
  simp only [CollatzResearch.WordTrace]
  refine ⟨121885349874247677334295645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81256899916165118222863763 121885349874247677334295645)
  ·
    refine ⟨45707006202842879000360867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121885349874247677334295645 45707006202842879000360867)
    ·
      refine ⟨68560509304264318500541301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45707006202842879000360867 68560509304264318500541301)
      ·
        refine ⟨6427547747274779859425747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68560509304264318500541301 6427547747274779859425747)
        ·
          refine ⟨9641321620912169789138621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427547747274779859425747 9641321620912169789138621)
          ·
            refine ⟨3615495607842063670926983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9641321620912169789138621 3615495607842063670926983)
            ·
              refine ⟨5423243411763095506390475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615495607842063670926983 5423243411763095506390475)
              ·
                refine ⟨8134865117644643259585713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423243411763095506390475 8134865117644643259585713)
                ·
                  refine ⟨6101148838233482444689285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134865117644643259585713 6101148838233482444689285)
                  ·
                    refine ⟨1143965407168777958379241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6101148838233482444689285 1143965407168777958379241)
                    ·
                      rfl

theorem cell22_3341797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_3341797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341797 prefixEnd_3341797 := by exact prefixLift 3341797
  have htrace : WordTrace (prefixWord ++ tailWord_3341797) baseStart_3341797 baseEnd_3341797 := by
    simpa [prefixWord, tailWord_3341797, baseEnd_3341797] using wordTrace_append hprefix tailTrace_3341797
  have hstable : (prefixWord ++ tailWord_3341797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341797).length < 2 ^ (prefixWord ++ tailWord_3341797).sum := by decide
  have hdescent : baseEnd_3341797 < baseStart_3341797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341823 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 5]
def baseStart_3341823 : Nat := 118140960795 + 3341823 * 2 ^ 59
def prefixEnd_3341823 : Nat := 4983230072969 + 3 ^ 40 * 3341823 * 2
def baseEnd_3341823 : Nat := 381324769166707519076387

theorem tailTrace_3341823 : CollatzResearch.WordTrace tailWord_3341823 prefixEnd_3341823 381324769166707519076387 := by
  unfold tailWord_3341823
  simp only [CollatzResearch.WordTrace]
  refine ⟨121886298172153483774742123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81257532114768989183161415 121886298172153483774742123)
  ·
    refine ⟨182829447258230225662113185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121886298172153483774742123 182829447258230225662113185)
    ·
      refine ⟨137122085443672669246584889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182829447258230225662113185 137122085443672669246584889)
      ·
        refine ⟨102841564082754501934938667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137122085443672669246584889 102841564082754501934938667)
        ·
          refine ⟨154262346124131752902408001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102841564082754501934938667 154262346124131752902408001)
          ·
            refine ⟨115696759593098814676806001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154262346124131752902408001 115696759593098814676806001)
            ·
              refine ⟨86772569694824111007604501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115696759593098814676806001 86772569694824111007604501)
              ·
                refine ⟨4067464204444880203481461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86772569694824111007604501 4067464204444880203481461)
                ·
                  refine ⟨381324769166707519076387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4067464204444880203481461 381324769166707519076387)
                  ·
                    rfl

theorem cell22_3341823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 5].length) (baseStart_3341823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341823 prefixEnd_3341823 := by exact prefixLift 3341823
  have htrace : WordTrace (prefixWord ++ tailWord_3341823) baseStart_3341823 baseEnd_3341823 := by
    simpa [prefixWord, tailWord_3341823, baseEnd_3341823] using wordTrace_append hprefix tailTrace_3341823
  have hstable : (prefixWord ++ tailWord_3341823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341823).length < 2 ^ (prefixWord ++ tailWord_3341823).sum := by decide
  have hdescent : baseEnd_3341823 < baseStart_3341823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341878 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3341878 : Nat := 118140960795 + 3341878 * 2 ^ 59
def prefixEnd_3341878 : Nat := 4983230072969 + 3 ^ 40 * 3341878 * 2
def baseEnd_3341878 : Nat := 1143993135124120747103993

theorem tailTrace_3341878 : CollatzResearch.WordTrace tailWord_3341878 prefixEnd_3341878 1143993135124120747103993 := by
  unfold tailWord_3341878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618019011684639260499643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81258869457969485445329525 7618019011684639260499643)
  ·
    refine ⟨11427028517526958890749465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7618019011684639260499643 11427028517526958890749465)
    ·
      refine ⟨8570271388145219168062099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11427028517526958890749465 8570271388145219168062099)
      ·
        refine ⟨12855407082217828752093149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8570271388145219168062099 12855407082217828752093149)
        ·
          refine ⟨4820777655831685782034931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12855407082217828752093149 4820777655831685782034931)
          ·
            refine ⟨7231166483747528673052397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820777655831685782034931 7231166483747528673052397)
            ·
              refine ⟨2711687431405323252394649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7231166483747528673052397 2711687431405323252394649)
              ·
                refine ⟨2033765573553992439295987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711687431405323252394649 2033765573553992439295987)
                ·
                  refine ⟨3050648360330988658943981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033765573553992439295987 3050648360330988658943981)
                  ·
                    refine ⟨1143993135124120747103993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050648360330988658943981 1143993135124120747103993)
                    ·
                      rfl

theorem cell22_3341878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3341878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341878 prefixEnd_3341878 := by exact prefixLift 3341878
  have htrace : WordTrace (prefixWord ++ tailWord_3341878) baseStart_3341878 baseEnd_3341878 := by
    simpa [prefixWord, tailWord_3341878, baseEnd_3341878] using wordTrace_append hprefix tailTrace_3341878
  have hstable : (prefixWord ++ tailWord_3341878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341878).length < 2 ^ (prefixWord ++ tailWord_3341878).sum := by decide
  have hdescent : baseEnd_3341878 < baseStart_3341878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341962 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_3341962 : Nat := 118140960795 + 3341962 * 2 ^ 59
def prefixEnd_3341962 : Nat := 4983230072969 + 3 ^ 40 * 3341962 * 2
def baseEnd_3341962 : Nat := 1144021890040772528003735

theorem tailTrace_3341962 : CollatzResearch.WordTrace tailWord_3341962 prefixEnd_3341962 1144021890040772528003735 := by
  unfold tailWord_3341962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30472841979662477628513035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81260911945766607009368093 30472841979662477628513035)
  ·
    refine ⟨45709262969493716442769553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30472841979662477628513035 45709262969493716442769553)
    ·
      refine ⟨34281947227120287332077165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45709262969493716442769553 34281947227120287332077165)
      ·
        refine ⟨12855730210170107749528937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34281947227120287332077165 12855730210170107749528937)
        ·
          refine ⟨9641797657627580812146703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12855730210170107749528937 9641797657627580812146703)
          ·
            refine ⟨14462696486441371218220055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641797657627580812146703 14462696486441371218220055)
            ·
              refine ⟨21694044729662056827330083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14462696486441371218220055 21694044729662056827330083)
              ·
                refine ⟨32541067094493085240995125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21694044729662056827330083 32541067094493085240995125)
                ·
                  refine ⟨3050725040108726741343293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32541067094493085240995125 3050725040108726741343293)
                  ·
                    refine ⟨1144021890040772528003735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050725040108726741343293 1144021890040772528003735)
                    ·
                      rfl

theorem cell22_3341962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_3341962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3341962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3341962 prefixEnd_3341962 := by exact prefixLift 3341962
  have htrace : WordTrace (prefixWord ++ tailWord_3341962) baseStart_3341962 baseEnd_3341962 := by
    simpa [prefixWord, tailWord_3341962, baseEnd_3341962] using wordTrace_append hprefix tailTrace_3341962
  have hstable : (prefixWord ++ tailWord_3341962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341962).length < 2 ^ (prefixWord ++ tailWord_3341962).sum := by decide
  have hdescent : baseEnd_3341962 < baseStart_3341962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342052 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_3342052 : Nat := 118140960795 + 3342052 * 2 ^ 59
def prefixEnd_3342052 : Nat := 4983230072969 + 3 ^ 40 * 3342052 * 2
def baseEnd_3342052 : Nat := 1144052698880042293253459

theorem tailTrace_3342052 : CollatzResearch.WordTrace tailWord_3342052 prefixEnd_3342052 1144052698880042293253459 := by
  unfold tailWord_3342052
  simp only [CollatzResearch.WordTrace]
  refine ⟨60947325244161927942414205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81263100325549237256552273 60947325244161927942414205)
  ·
    refine ⟨22855246966560722978405327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60947325244161927942414205 22855246966560722978405327)
    ·
      refine ⟨34282870449841084467607991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22855246966560722978405327 34282870449841084467607991)
      ·
        refine ⟨51424305674761626701411987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34282870449841084467607991 51424305674761626701411987)
        ·
          refine ⟨77136458512142440052117981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51424305674761626701411987 77136458512142440052117981)
          ·
            refine ⟨28926171942053415019544243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77136458512142440052117981 28926171942053415019544243)
            ·
              refine ⟨43389257913080122529316365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28926171942053415019544243 43389257913080122529316365)
              ·
                refine ⟨16270971717405045948493637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43389257913080122529316365 16270971717405045948493637)
                ·
                  refine ⟨3050807197013446115342557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16270971717405045948493637 3050807197013446115342557)
                  ·
                    refine ⟨1144052698880042293253459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050807197013446115342557 1144052698880042293253459)
                    ·
                      rfl

theorem cell22_3342052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_3342052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342052 prefixEnd_3342052 := by exact prefixLift 3342052
  have htrace : WordTrace (prefixWord ++ tailWord_3342052) baseStart_3342052 baseEnd_3342052 := by
    simpa [prefixWord, tailWord_3342052, baseEnd_3342052] using wordTrace_append hprefix tailTrace_3342052
  have hstable : (prefixWord ++ tailWord_3342052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342052).length < 2 ^ (prefixWord ++ tailWord_3342052).sum := by decide
  have hdescent : baseEnd_3342052 < baseStart_3342052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342065 : List Nat := [1, 2, 2, 2, 2, 3, 1, 9]
def baseStart_3342065 : Nat := 118140960795 + 3342065 * 2 ^ 59
def prefixEnd_3342065 : Nat := 4983230072969 + 3 ^ 40 * 3342065 * 2
def baseEnd_3342065 : Nat := 127117461005079399186491

theorem tailTrace_3342065 : CollatzResearch.WordTrace tailWord_3342065 prefixEnd_3342065 127117461005079399186491 := by
  unfold tailWord_3342065
  simp only [CollatzResearch.WordTrace]
  refine ⟨121895124637276759105051649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81263416424851172736701099 121895124637276759105051649)
  ·
    refine ⟨91421343477957569328788737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121895124637276759105051649 91421343477957569328788737)
    ·
      refine ⟨68566007608468176996591553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91421343477957569328788737 68566007608468176996591553)
      ·
        refine ⟨51424505706351132747443665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68566007608468176996591553 51424505706351132747443665)
        ·
          refine ⟨38568379279763349560582749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51424505706351132747443665 38568379279763349560582749)
          ·
            refine ⟨14463142229911256085218531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38568379279763349560582749 14463142229911256085218531)
            ·
              refine ⟨21694713344866884127827797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14463142229911256085218531 21694713344866884127827797)
              ·
                refine ⟨127117461005079399186491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21694713344866884127827797 127117461005079399186491)
                ·
                  rfl

theorem cell22_3342065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 9].length) (baseStart_3342065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342065 prefixEnd_3342065 := by exact prefixLift 3342065
  have htrace : WordTrace (prefixWord ++ tailWord_3342065) baseStart_3342065 baseEnd_3342065 := by
    simpa [prefixWord, tailWord_3342065, baseEnd_3342065] using wordTrace_append hprefix tailTrace_3342065
  have hstable : (prefixWord ++ tailWord_3342065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342065).length < 2 ^ (prefixWord ++ tailWord_3342065).sum := by decide
  have hdescent : baseEnd_3342065 < baseStart_3342065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342082 : List Nat := [3, 4, 1, 1, 1, 1, 1, 10]
def baseStart_3342082 : Nat := 118140960795 + 3342082 * 2 ^ 59
def prefixEnd_3342082 : Nat := 4983230072969 + 3 ^ 40 * 3342082 * 2
def baseEnd_3342082 : Nat := 127118107610348023889263

theorem tailTrace_3342082 : CollatzResearch.WordTrace tailWord_3342082 prefixEnd_3342082 127118107610348023889263 := by
  unfold tailWord_3342082
  simp only [CollatzResearch.WordTrace]
  refine ⟨30473936169553792752105125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81263829785476780672280333 30473936169553792752105125)
  ·
    refine ⟨5713863031791336141019711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30473936169553792752105125 5713863031791336141019711)
    ·
      refine ⟨8570794547687004211529567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5713863031791336141019711 8570794547687004211529567)
      ·
        refine ⟨12856191821530506317294351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8570794547687004211529567 12856191821530506317294351)
        ·
          refine ⟨19284287732295759475941527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12856191821530506317294351 19284287732295759475941527)
          ·
            refine ⟨28926431598443639213912291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284287732295759475941527 28926431598443639213912291)
            ·
              refine ⟨43389647397665458820868437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28926431598443639213912291 43389647397665458820868437)
              ·
                refine ⟨127118107610348023889263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43389647397665458820868437 127118107610348023889263)
                ·
                  rfl

theorem cell22_3342082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_3342082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342082 prefixEnd_3342082 := by exact prefixLift 3342082
  have htrace : WordTrace (prefixWord ++ tailWord_3342082) baseStart_3342082 baseEnd_3342082 := by
    simpa [prefixWord, tailWord_3342082, baseEnd_3342082] using wordTrace_append hprefix tailTrace_3342082
  have hstable : (prefixWord ++ tailWord_3342082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342082).length < 2 ^ (prefixWord ++ tailWord_3342082).sum := by decide
  have hdescent : baseEnd_3342082 < baseStart_3342082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342084 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_3342084 : Nat := 118140960795 + 3342084 * 2 ^ 59
def prefixEnd_3342084 : Nat := 4983230072969 + 3 ^ 40 * 3342084 * 2
def baseEnd_3342084 : Nat := 1144063653134004876453361

theorem tailTrace_3342084 : CollatzResearch.WordTrace tailWord_3342084 prefixEnd_3342084 1144063653134004876453361 := by
  unfold tailWord_3342084
  simp only [CollatzResearch.WordTrace]
  refine ⟨60947908812103962674996653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81263878416138616899995537 60947908812103962674996653)
  ·
    refine ⟨22855465804538986003123745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60947908812103962674996653 22855465804538986003123745)
    ·
      refine ⟨17141599353404239502342809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22855465804538986003123745 17141599353404239502342809)
      ·
        refine ⟨12856199515053179626757107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17141599353404239502342809 12856199515053179626757107)
        ·
          refine ⟨19284299272579769440135661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12856199515053179626757107 19284299272579769440135661)
          ·
            refine ⟨7231612227217413540050873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19284299272579769440135661 7231612227217413540050873)
            ·
              refine ⟨5423709170413060155038155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7231612227217413540050873 5423709170413060155038155)
              ·
                refine ⟨8135563755619590232557233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423709170413060155038155 8135563755619590232557233)
                ·
                  refine ⟨6101672816714692674417925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8135563755619590232557233 6101672816714692674417925)
                  ·
                    refine ⟨1144063653134004876453361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6101672816714692674417925 1144063653134004876453361)
                    ·
                      rfl

theorem cell22_3342084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_3342084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342084 prefixEnd_3342084 := by exact prefixLift 3342084
  have htrace : WordTrace (prefixWord ++ tailWord_3342084) baseStart_3342084 baseEnd_3342084 := by
    simpa [prefixWord, tailWord_3342084, baseEnd_3342084] using wordTrace_append hprefix tailTrace_3342084
  have hstable : (prefixWord ++ tailWord_3342084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342084).length < 2 ^ (prefixWord ++ tailWord_3342084).sum := by decide
  have hdescent : baseEnd_3342084 < baseStart_3342084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342114 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3342114 : Nat := 118140960795 + 3342114 * 2 ^ 59
def prefixEnd_3342114 : Nat := 4983230072969 + 3 ^ 40 * 3342114 * 2
def baseEnd_3342114 : Nat := 1144073922747094798203269

theorem tailTrace_3342114 : CollatzResearch.WordTrace tailWord_3342114 prefixEnd_3342114 1144073922747094798203269 := by
  unfold tailWord_3342114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474227953524810118396349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81264607876066160315723597 30474227953524810118396349)
  ·
    refine ⟨11427835482571803794398631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30474227953524810118396349 11427835482571803794398631)
    ·
      refine ⟨17141753223857705691597947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11427835482571803794398631 17141753223857705691597947)
      ·
        refine ⟨25712629835786558537396921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17141753223857705691597947 25712629835786558537396921)
        ·
          refine ⟨19284472376839918903047691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25712629835786558537396921 19284472376839918903047691)
          ·
            refine ⟨28926708565259878354571537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284472376839918903047691 28926708565259878354571537)
            ·
              refine ⟨21695031423944908765928653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28926708565259878354571537 21695031423944908765928653)
              ·
                refine ⟨8135636783979340787223245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21695031423944908765928653 8135636783979340787223245)
                ·
                  refine ⟨3050863793992252795208717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8135636783979340787223245 3050863793992252795208717)
                  ·
                    refine ⟨1144073922747094798203269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050863793992252795208717 1144073922747094798203269)
                    ·
                      rfl

theorem cell22_3342114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3342114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342114 prefixEnd_3342114 := by exact prefixLift 3342114
  have htrace : WordTrace (prefixWord ++ tailWord_3342114) baseStart_3342114 baseEnd_3342114 := by
    simpa [prefixWord, tailWord_3342114, baseEnd_3342114] using wordTrace_append hprefix tailTrace_3342114
  have hstable : (prefixWord ++ tailWord_3342114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342114).length < 2 ^ (prefixWord ++ tailWord_3342114).sum := by decide
  have hdescent : baseEnd_3342114 < baseStart_3342114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342202 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_3342202 : Nat := 118140960795 + 3342202 * 2 ^ 59
def prefixEnd_3342202 : Nat := 4983230072969 + 3 ^ 40 * 3342202 * 2
def baseEnd_3342202 : Nat := 1144104046945491902002999

theorem tailTrace_3342202 : CollatzResearch.WordTrace tailWord_3342202 prefixEnd_3342202 1144104046945491902002999 := by
  unfold tailWord_3342202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30475030359445107875697215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81266747625186954335192573 30475030359445107875697215)
  ·
    refine ⟨45712545539167661813545823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30475030359445107875697215 45712545539167661813545823)
    ·
      refine ⟨68568818308751492720318735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45712545539167661813545823 68568818308751492720318735)
      ·
        refine ⟨102853227463127239080478103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68568818308751492720318735 102853227463127239080478103)
        ·
          refine ⟨154279841194690858620717155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102853227463127239080478103 154279841194690858620717155)
          ·
            refine ⟨231419761792036287931075733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154279841194690858620717155 231419761792036287931075733)
            ·
              refine ⟨10847801334001700996769175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231419761792036287931075733 10847801334001700996769175)
              ·
                refine ⟨16271702001002551495153763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10847801334001700996769175 16271702001002551495153763)
                ·
                  refine ⟨24407553001503827242730645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16271702001002551495153763 24407553001503827242730645)
                  ·
                    refine ⟨1144104046945491902002999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24407553001503827242730645 1144104046945491902002999)
                    ·
                      rfl

theorem cell22_3342202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_3342202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342202 prefixEnd_3342202 := by exact prefixLift 3342202
  have htrace : WordTrace (prefixWord ++ tailWord_3342202) baseStart_3342202 baseEnd_3342202 := by
    simpa [prefixWord, tailWord_3342202, baseEnd_3342202] using wordTrace_append hprefix tailTrace_3342202
  have hstable : (prefixWord ++ tailWord_3342202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342202).length < 2 ^ (prefixWord ++ tailWord_3342202).sum := by decide
  have hdescent : baseEnd_3342202 < baseStart_3342202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342234 : List Nat := [3, 1, 1, 4, 2, 2, 2, 7]
def baseStart_3342234 : Nat := 118140960795 + 3342234 * 2 ^ 59
def prefixEnd_3342234 : Nat := 4983230072969 + 3 ^ 40 * 3342234 * 2
def baseEnd_3342234 : Nat := 127123889022161609466989

theorem tailTrace_3342234 : CollatzResearch.WordTrace tailWord_3342234 prefixEnd_3342234 127123889022161609466989 := by
  unfold tailWord_3342234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30475322143416125241988439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81267525715776333978635837 30475322143416125241988439)
  ·
    refine ⟨45712983215124187862982659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30475322143416125241988439 45712983215124187862982659)
    ·
      refine ⟨68569474822686281794473989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45712983215124187862982659 68569474822686281794473989)
      ·
        refine ⟨12856776529253677836463873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68569474822686281794473989 12856776529253677836463873)
        ·
          refine ⟨9642582396940258377347905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12856776529253677836463873 9642582396940258377347905)
          ·
            refine ⟨7231936797705193783010929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9642582396940258377347905 7231936797705193783010929)
            ·
              refine ⟨5423952598278895337258197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7231936797705193783010929 5423952598278895337258197)
              ·
                refine ⟨127123889022161609466989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5423952598278895337258197 127123889022161609466989)
                ·
                  rfl

theorem cell22_3342234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_3342234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342234 prefixEnd_3342234 := by exact prefixLift 3342234
  have htrace : WordTrace (prefixWord ++ tailWord_3342234) baseStart_3342234 baseEnd_3342234 := by
    simpa [prefixWord, tailWord_3342234, baseEnd_3342234] using wordTrace_append hprefix tailTrace_3342234
  have hstable : (prefixWord ++ tailWord_3342234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342234).length < 2 ^ (prefixWord ++ tailWord_3342234).sum := by decide
  have hdescent : baseEnd_3342234 < baseStart_3342234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342317 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_3342317 : Nat := 118140960795 + 3342317 * 2 ^ 59
def prefixEnd_3342317 : Nat := 4983230072969 + 3 ^ 40 * 3342317 * 2
def baseEnd_3342317 : Nat := 1144143413795669935377647

theorem tailTrace_3342317 : CollatzResearch.WordTrace tailWord_3342317 prefixEnd_3342317 1144143413795669935377647 := by
  unfold tailWord_3342317
  simp only [CollatzResearch.WordTrace]
  refine ⟨121904315832363806143225205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81269543888242537428816803 121904315832363806143225205)
  ·
    refine ⟨11428529609284106825927363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121904315832363806143225205 11428529609284106825927363)
    ·
      refine ⟨17142794413926160238891045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11428529609284106825927363 17142794413926160238891045)
      ·
        refine ⟨3214273952611155044792071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17142794413926160238891045 3214273952611155044792071)
        ·
          refine ⟨4821410928916732567188107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214273952611155044792071 4821410928916732567188107)
          ·
            refine ⟨7232116393375098850782161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821410928916732567188107 7232116393375098850782161)
            ·
              refine ⟨5424087295031324138086621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7232116393375098850782161 5424087295031324138086621)
              ·
                refine ⟨2034032735636746551782483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5424087295031324138086621 2034032735636746551782483)
                ·
                  refine ⟨3051049103455119827673725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034032735636746551782483 3051049103455119827673725)
                  ·
                    refine ⟨1144143413795669935377647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051049103455119827673725 1144143413795669935377647)
                    ·
                      rfl

theorem cell22_3342317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_3342317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342317 prefixEnd_3342317 := by exact prefixLift 3342317
  have htrace : WordTrace (prefixWord ++ tailWord_3342317) baseStart_3342317 baseEnd_3342317 := by
    simpa [prefixWord, tailWord_3342317, baseEnd_3342317] using wordTrace_append hprefix tailTrace_3342317
  have hstable : (prefixWord ++ tailWord_3342317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342317).length < 2 ^ (prefixWord ++ tailWord_3342317).sum := by decide
  have hdescent : baseEnd_3342317 < baseStart_3342317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342341 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 4]
def baseStart_3342341 : Nat := 118140960795 + 3342341 * 2 ^ 59
def prefixEnd_3342341 : Nat := 4983230072969 + 3 ^ 40 * 3342341 * 2
def baseEnd_3342341 : Nat := 381383876495380624259191

theorem tailTrace_3342341 : CollatzResearch.WordTrace tailWord_3342341 prefixEnd_3342341 381383876495380624259191 := by
  unfold tailWord_3342341
  simp only [CollatzResearch.WordTrace]
  refine ⟨121905191184276858242098877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81270127456184572161399251 121905191184276858242098877)
  ·
    refine ⟨45714446694103821840787079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121905191184276858242098877 45714446694103821840787079)
    ·
      refine ⟨68571670041155732761180619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45714446694103821840787079 68571670041155732761180619)
      ·
        refine ⟨102857505061733599141770929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68571670041155732761180619 102857505061733599141770929)
        ·
          refine ⟨77143128796300199356328197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102857505061733599141770929 77143128796300199356328197)
          ·
            refine ⟨14464336649306287379311537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77143128796300199356328197 14464336649306287379311537)
            ·
              refine ⟨10848252486979715534483653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14464336649306287379311537 10848252486979715534483653)
              ·
                refine ⟨2034047341308696662715685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10848252486979715534483653 2034047341308696662715685)
                ·
                  refine ⟨381383876495380624259191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034047341308696662715685 381383876495380624259191)
                  ·
                    rfl

theorem cell22_3342341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_3342341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342341 prefixEnd_3342341 := by exact prefixLift 3342341
  have htrace : WordTrace (prefixWord ++ tailWord_3342341) baseStart_3342341 baseEnd_3342341 := by
    simpa [prefixWord, tailWord_3342341, baseEnd_3342341] using wordTrace_append hprefix tailTrace_3342341
  have hstable : (prefixWord ++ tailWord_3342341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342341).length < 2 ^ (prefixWord ++ tailWord_3342341).sum := by decide
  have hdescent : baseEnd_3342341 < baseStart_3342341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342446 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3342446 : Nat := 118140960795 + 3342446 * 2 ^ 59
def prefixEnd_3342446 : Nat := 4983230072969 + 3 ^ 40 * 3342446 * 2
def baseEnd_3342446 : Nat := 1144187573131956598902251

theorem tailTrace_3342446 : CollatzResearch.WordTrace tailWord_3342446 prefixEnd_3342446 1144187573131956598902251 := by
  unfold tailWord_3342446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15238627606112057646833899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81272680565930974116447461 15238627606112057646833899)
  ·
    refine ⟨22857941409168086470250849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15238627606112057646833899 22857941409168086470250849)
    ·
      refine ⟨17143456056876064852688137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22857941409168086470250849 17143456056876064852688137)
      ·
        refine ⟨12857592042657048639516103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17143456056876064852688137 12857592042657048639516103)
        ·
          refine ⟨19286388063985572959274155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12857592042657048639516103 19286388063985572959274155)
          ·
            refine ⟨28929582095978359438911233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19286388063985572959274155 28929582095978359438911233)
            ·
              refine ⟨21697186571983769579183425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28929582095978359438911233 21697186571983769579183425)
              ·
                refine ⟨16272889928987827184387569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21697186571983769579183425 16272889928987827184387569)
                ·
                  refine ⟨12204667446740870388290677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16272889928987827184387569 12204667446740870388290677)
                  ·
                    refine ⟨1144187573131956598902251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12204667446740870388290677 1144187573131956598902251)
                    ·
                      rfl

theorem cell22_3342446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3342446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342446 prefixEnd_3342446 := by exact prefixLift 3342446
  have htrace : WordTrace (prefixWord ++ tailWord_3342446) baseStart_3342446 baseEnd_3342446 := by
    simpa [prefixWord, tailWord_3342446, baseEnd_3342446] using wordTrace_append hprefix tailTrace_3342446
  have hstable : (prefixWord ++ tailWord_3342446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342446).length < 2 ^ (prefixWord ++ tailWord_3342446).sum := by decide
  have hdescent : baseEnd_3342446 < baseStart_3342446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342461 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_3342461 : Nat := 118140960795 + 3342461 * 2 ^ 59
def prefixEnd_3342461 : Nat := 4983230072969 + 3 ^ 40 * 3342461 * 2
def baseEnd_3342461 : Nat := 1144192707938501559777205

theorem tailTrace_3342461 : CollatzResearch.WordTrace tailWord_3342461 prefixEnd_3342461 1144192707938501559777205 := by
  unfold tailWord_3342461
  simp only [CollatzResearch.WordTrace]
  refine ⟨121909567943842118736467237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81273045295894745824311491 121909567943842118736467237)
  ·
    refine ⟨22858043989470397263087607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121909567943842118736467237 22858043989470397263087607)
    ·
      refine ⟨34287065984205595894631411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22858043989470397263087607 34287065984205595894631411)
      ·
        refine ⟨51430598976308393841947117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34287065984205595894631411 51430598976308393841947117)
        ·
          refine ⟨19286474616115647690730169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51430598976308393841947117 19286474616115647690730169)
          ·
            refine ⟨14464855962086735768047627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19286474616115647690730169 14464855962086735768047627)
            ·
              refine ⟨21697283943130103652071441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464855962086735768047627 21697283943130103652071441)
              ·
                refine ⟨16272962957347577739053581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21697283943130103652071441 16272962957347577739053581)
                ·
                  refine ⟨6102361109005341652145093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16272962957347577739053581 6102361109005341652145093)
                  ·
                    refine ⟨1144192707938501559777205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6102361109005341652145093 1144192707938501559777205)
                    ·
                      rfl

theorem cell22_3342461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_3342461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342461 prefixEnd_3342461 := by exact prefixLift 3342461
  have htrace : WordTrace (prefixWord ++ tailWord_3342461) baseStart_3342461 baseEnd_3342461 := by
    simpa [prefixWord, tailWord_3342461, baseEnd_3342461] using wordTrace_append hprefix tailTrace_3342461
  have hstable : (prefixWord ++ tailWord_3342461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342461).length < 2 ^ (prefixWord ++ tailWord_3342461).sum := by decide
  have hdescent : baseEnd_3342461 < baseStart_3342461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342493 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 4]
def baseStart_3342493 : Nat := 118140960795 + 3342493 * 2 ^ 59
def prefixEnd_3342493 : Nat := 4983230072969 + 3 ^ 40 * 3342493 * 2
def baseEnd_3342493 : Nat := 381401220730821380992369

theorem tailTrace_3342493 : CollatzResearch.WordTrace tailWord_3342493 prefixEnd_3342493 381401220730821380992369 := by
  unfold tailWord_3342493
  simp only [CollatzResearch.WordTrace]
  refine ⟨121910735079726188201632133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81273823386484125467754755 121910735079726188201632133)
  ·
    refine ⟨22858262827448660287806025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121910735079726188201632133 22858262827448660287806025)
    ·
      refine ⟨17143697120586495215854519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22858262827448660287806025 17143697120586495215854519)
      ·
        refine ⟨25715545680879742823781779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17143697120586495215854519 25715545680879742823781779)
        ·
          refine ⟨38573318521319614235672669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25715545680879742823781779 38573318521319614235672669)
          ·
            refine ⟨14464994445494855338377251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38573318521319614235672669 14464994445494855338377251)
            ·
              refine ⟨21697491668242283007565877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464994445494855338377251 21697491668242283007565877)
              ·
                refine ⟨2034139843897714031959301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21697491668242283007565877 2034139843897714031959301)
                ·
                  refine ⟨381401220730821380992369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034139843897714031959301 381401220730821380992369)
                  ·
                    rfl

theorem cell22_3342493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_3342493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342493 prefixEnd_3342493 := by exact prefixLift 3342493
  have htrace : WordTrace (prefixWord ++ tailWord_3342493) baseStart_3342493 baseEnd_3342493 := by
    simpa [prefixWord, tailWord_3342493, baseEnd_3342493] using wordTrace_append hprefix tailTrace_3342493
  have hstable : (prefixWord ++ tailWord_3342493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342493).length < 2 ^ (prefixWord ++ tailWord_3342493).sum := by decide
  have hdescent : baseEnd_3342493 < baseStart_3342493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342495 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 1, 4]
def baseStart_3342495 : Nat := 118140960795 + 3342495 * 2 ^ 59
def prefixEnd_3342495 : Nat := 4983230072969 + 3 ^ 40 * 3342495 * 2
def baseEnd_3342495 : Nat := 1144204346833336804427101

theorem tailTrace_3342495 : CollatzResearch.WordTrace tailWord_3342495 prefixEnd_3342495 1144204346833336804427101 := by
  unfold tailWord_3342495
  simp only [CollatzResearch.WordTrace]
  refine ⟨121910808025718942543204939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81273872017145961695469959 121910808025718942543204939)
  ·
    refine ⟨182866212038578413814807409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121910808025718942543204939 182866212038578413814807409)
    ·
      refine ⟨137149659028933810361105557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182866212038578413814807409 137149659028933810361105557)
      ·
        refine ⟨6428890266981272360676823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137149659028933810361105557 6428890266981272360676823)
        ·
          refine ⟨9643335400471908541015235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6428890266981272360676823 9643335400471908541015235)
          ·
            refine ⟨14465003100707862811522853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9643335400471908541015235 14465003100707862811522853)
            ·
              refine ⟨2712188081382724277160535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14465003100707862811522853 2712188081382724277160535)
              ·
                refine ⟨4068282122074086415740803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712188081382724277160535 4068282122074086415740803)
                ·
                  refine ⟨6102423183111129623611205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068282122074086415740803 6102423183111129623611205)
                  ·
                    refine ⟨1144204346833336804427101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6102423183111129623611205 1144204346833336804427101)
                    ·
                      rfl

theorem cell22_3342495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_3342495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342495 prefixEnd_3342495 := by exact prefixLift 3342495
  have htrace : WordTrace (prefixWord ++ tailWord_3342495) baseStart_3342495 baseEnd_3342495 := by
    simpa [prefixWord, tailWord_3342495, baseEnd_3342495] using wordTrace_append hprefix tailTrace_3342495
  have hstable : (prefixWord ++ tailWord_3342495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342495).length < 2 ^ (prefixWord ++ tailWord_3342495).sum := by decide
  have hdescent : baseEnd_3342495 < baseStart_3342495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342613 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3342613 : Nat := 118140960795 + 3342613 * 2 ^ 59
def prefixEnd_3342613 : Nat := 4983230072969 + 3 ^ 40 * 3342613 * 2
def baseEnd_3342613 : Nat := 1144244740644823829976739

theorem tailTrace_3342613 : CollatzResearch.WordTrace tailWord_3342613 prefixEnd_3342613 1144244740644823829976739 := by
  unfold tailWord_3342613
  simp only [CollatzResearch.WordTrace]
  refine ⟨121915111839291448696000493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81276741226194299130666995 121915111839291448696000493)
  ·
    refine ⟨45718166939734293261000185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121915111839291448696000493 45718166939734293261000185)
    ·
      refine ⟨34288625204800719945750139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45718166939734293261000185 34288625204800719945750139)
      ·
        refine ⟨51432937807201079918625209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34288625204800719945750139 51432937807201079918625209)
        ·
          refine ⟨38574703355400809938968907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51432937807201079918625209 38574703355400809938968907)
          ·
            refine ⟨57862055033101214908453361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38574703355400809938968907 57862055033101214908453361)
            ·
              refine ⟨43396541274825911181340021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57862055033101214908453361 43396541274825911181340021)
              ·
                refine ⟨4068425744514929173250627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43396541274825911181340021 4068425744514929173250627)
                ·
                  refine ⟨6102638616772393759875941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068425744514929173250627 6102638616772393759875941)
                  ·
                    refine ⟨1144244740644823829976739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6102638616772393759875941 1144244740644823829976739)
                    ·
                      rfl

theorem cell22_3342613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3342613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342613 prefixEnd_3342613 := by exact prefixLift 3342613
  have htrace : WordTrace (prefixWord ++ tailWord_3342613) baseStart_3342613 baseEnd_3342613 := by
    simpa [prefixWord, tailWord_3342613, baseEnd_3342613] using wordTrace_append hprefix tailTrace_3342613
  have hstable : (prefixWord ++ tailWord_3342613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342613).length < 2 ^ (prefixWord ++ tailWord_3342613).sum := by decide
  have hdescent : baseEnd_3342613 < baseStart_3342613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342621 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3342621 : Nat := 118140960795 + 3342621 * 2 ^ 59
def prefixEnd_3342621 : Nat := 4983230072969 + 3 ^ 40 * 3342621 * 2
def baseEnd_3342621 : Nat := 1144247479208314475776715

theorem tailTrace_3342621 : CollatzResearch.WordTrace tailWord_3342621 prefixEnd_3342621 1144247479208314475776715 := by
  unfold tailWord_3342621
  simp only [CollatzResearch.WordTrace]
  refine ⟨121915403623262466062291717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81276935748841644041527811 121915403623262466062291717)
  ·
    refine ⟨22859138179361712386679697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121915403623262466062291717 22859138179361712386679697)
    ·
      refine ⟨17144353634521284290009773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22859138179361712386679697 17144353634521284290009773)
      ·
        refine ⟨6429132612945481608753665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17144353634521284290009773 6429132612945481608753665)
        ·
          refine ⟨4821849459709111206565249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6429132612945481608753665 4821849459709111206565249)
          ·
            refine ⟨3616387094781833404923937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4821849459709111206565249 3616387094781833404923937)
            ·
              refine ⟨2712290321086375053692953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616387094781833404923937 2712290321086375053692953)
              ·
                refine ⟨2034217740814781290269715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712290321086375053692953 2034217740814781290269715)
                ·
                  refine ⟨3051326611222171935404573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034217740814781290269715 3051326611222171935404573)
                  ·
                    refine ⟨1144247479208314475776715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051326611222171935404573 1144247479208314475776715)
                    ·
                      rfl

theorem cell22_3342621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3342621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342621 prefixEnd_3342621 := by exact prefixLift 3342621
  have htrace : WordTrace (prefixWord ++ tailWord_3342621) baseStart_3342621 baseEnd_3342621 := by
    simpa [prefixWord, tailWord_3342621, baseEnd_3342621] using wordTrace_append hprefix tailTrace_3342621
  have hstable : (prefixWord ++ tailWord_3342621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342621).length < 2 ^ (prefixWord ++ tailWord_3342621).sum := by decide
  have hdescent : baseEnd_3342621 < baseStart_3342621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342643 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 1, 5]
def baseStart_3342643 : Nat := 118140960795 + 3342643 * 2 ^ 59
def prefixEnd_3342643 : Nat := 4983230072969 + 3 ^ 40 * 3342643 * 2
def baseEnd_3342643 : Nat := 1144255010257913751726647

theorem tailTrace_3342643 : CollatzResearch.WordTrace tailWord_3342643 prefixEnd_3342643 1144255010257913751726647 := by
  unfold tailWord_3342643
  simp only [CollatzResearch.WordTrace]
  refine ⟨121916206029182763819592583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81277470686121842546395055 121916206029182763819592583)
  ·
    refine ⟨182874309043774145729388875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121916206029182763819592583 182874309043774145729388875)
    ·
      refine ⟨274311463565661218594083313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182874309043774145729388875 274311463565661218594083313)
      ·
        refine ⟨205733597674245913945562485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274311463565661218594083313 205733597674245913945562485)
        ·
          refine ⟨19287524781960554432396483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205733597674245913945562485 19287524781960554432396483)
          ·
            refine ⟨28931287172940831648594725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287524781960554432396483 28931287172940831648594725)
            ·
              refine ⟨5424616344926405934111511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28931287172940831648594725 5424616344926405934111511)
              ·
                refine ⟨8136924517389608901167267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424616344926405934111511 8136924517389608901167267)
                ·
                  refine ⟨12205386776084413351750901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8136924517389608901167267 12205386776084413351750901)
                  ·
                    refine ⟨1144255010257913751726647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12205386776084413351750901 1144255010257913751726647)
                    ·
                      rfl

theorem cell22_3342643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].length) (baseStart_3342643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342643 prefixEnd_3342643 := by exact prefixLift 3342643
  have htrace : WordTrace (prefixWord ++ tailWord_3342643) baseStart_3342643 baseEnd_3342643 := by
    simpa [prefixWord, tailWord_3342643, baseEnd_3342643] using wordTrace_append hprefix tailTrace_3342643
  have hstable : (prefixWord ++ tailWord_3342643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342643).length < 2 ^ (prefixWord ++ tailWord_3342643).sum := by decide
  have hdescent : baseEnd_3342643 < baseStart_3342643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342752 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 5]
def baseStart_3342752 : Nat := 118140960795 + 3342752 * 2 ^ 59
def prefixEnd_3342752 : Nat := 4983230072969 + 3 ^ 40 * 3342752 * 2
def baseEnd_3342752 : Nat := 381430774395157933583771

theorem tailTrace_3342752 : CollatzResearch.WordTrace tailWord_3342752 prefixEnd_3342752 381430774395157933583771 := by
  unfold tailWord_3342752
  simp only [CollatzResearch.WordTrace]
  refine ⟨60960090792893937717655255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81280121057191916956873673 60960090792893937717655255)
  ·
    refine ⟨91440136189340906576482883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60960090792893937717655255 91440136189340906576482883)
    ·
      refine ⟨137160204284011359864724325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91440136189340906576482883 137160204284011359864724325)
      ·
        refine ⟨25717538303252129974635811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137160204284011359864724325 25717538303252129974635811)
        ·
          refine ⟨38576307454878194961953717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25717538303252129974635811 38576307454878194961953717)
          ·
            refine ⟨3616528823894830777683161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38576307454878194961953717 3616528823894830777683161)
            ·
              refine ⟨2712396617921123083262371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616528823894830777683161 2712396617921123083262371)
              ·
                refine ⟨4068594926881684624893557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712396617921123083262371 4068594926881684624893557)
                ·
                  refine ⟨381430774395157933583771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4068594926881684624893557 381430774395157933583771)
                  ·
                    rfl

theorem cell22_3342752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_3342752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342752 prefixEnd_3342752 := by exact prefixLift 3342752
  have htrace : WordTrace (prefixWord ++ tailWord_3342752) baseStart_3342752 baseEnd_3342752 := by
    simpa [prefixWord, tailWord_3342752, baseEnd_3342752] using wordTrace_append hprefix tailTrace_3342752
  have hstable : (prefixWord ++ tailWord_3342752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342752).length < 2 ^ (prefixWord ++ tailWord_3342752).sum := by decide
  have hdescent : baseEnd_3342752 < baseStart_3342752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342840 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_3342840 : Nat := 118140960795 + 3342840 * 2 ^ 59
def prefixEnd_3342840 : Nat := 4983230072969 + 3 ^ 40 * 3342840 * 2
def baseEnd_3342840 : Nat := 1144322447383870904551043

theorem tailTrace_3342840 : CollatzResearch.WordTrace tailWord_3342840 prefixEnd_3342840 1144322447383870904551043 := by
  unfold tailWord_3342840
  simp only [CollatzResearch.WordTrace]
  refine ⟨60961695604734533232256987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81282260806312710976342649 60961695604734533232256987)
  ·
    refine ⟨91442543407101799848385481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60961695604734533232256987 91442543407101799848385481)
    ·
      refine ⟨68581907555326349886289111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91442543407101799848385481 68581907555326349886289111)
      ·
        refine ⟨102872861332989524829433667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68581907555326349886289111 102872861332989524829433667)
        ·
          refine ⟨154309291999484287244150501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102872861332989524829433667 154309291999484287244150501)
          ·
            refine ⟨28932992249903303858278219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154309291999484287244150501 28932992249903303858278219)
            ·
              refine ⟨43399488374854955787417329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28932992249903303858278219 43399488374854955787417329)
              ·
                refine ⟨32549616281141216840562997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43399488374854955787417329 32549616281141216840562997)
                ·
                  refine ⟨3051526526356989078802781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32549616281141216840562997 3051526526356989078802781)
                  ·
                    refine ⟨1144322447383870904551043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051526526356989078802781 1144322447383870904551043)
                    ·
                      rfl

theorem cell22_3342840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_3342840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342840 prefixEnd_3342840 := by exact prefixLift 3342840
  have htrace : WordTrace (prefixWord ++ tailWord_3342840) baseStart_3342840 baseEnd_3342840 := by
    simpa [prefixWord, tailWord_3342840, baseEnd_3342840] using wordTrace_append hprefix tailTrace_3342840
  have hstable : (prefixWord ++ tailWord_3342840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342840).length < 2 ^ (prefixWord ++ tailWord_3342840).sum := by decide
  have hdescent : baseEnd_3342840 < baseStart_3342840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342960 : List Nat := [2, 1, 1, 1, 7, 10]
def baseStart_3342960 : Nat := 118140960795 + 3342960 * 2 ^ 59
def prefixEnd_3342960 : Nat := 4983230072969 + 3 ^ 40 * 3342960 * 2
def baseEnd_3342960 : Nat := 14127944763410254216675

theorem tailTrace_3342960 : CollatzResearch.WordTrace tailWord_3342960 prefixEnd_3342960 14127944763410254216675 := by
  unfold tailWord_3342960
  simp only [CollatzResearch.WordTrace]
  refine ⟨60963883984517163479441167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81285178646022884639254889 60963883984517163479441167)
  ·
    refine ⟨91445825976775745219161751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60963883984517163479441167 91445825976775745219161751)
    ·
      refine ⟨137168738965163617828742627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91445825976775745219161751 137168738965163617828742627)
      ·
        refine ⟨205753108447745426743113941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137168738965163617828742627 205753108447745426743113941)
        ·
          refine ⟨4822338479244033439291733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 205753108447745426743113941 4822338479244033439291733)
          ·
            refine ⟨14127944763410254216675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4822338479244033439291733 14127944763410254216675)
            ·
              rfl

theorem cell22_3342960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 10].length) (baseStart_3342960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342960 prefixEnd_3342960 := by exact prefixLift 3342960
  have htrace : WordTrace (prefixWord ++ tailWord_3342960) baseStart_3342960 baseEnd_3342960 := by
    simpa [prefixWord, tailWord_3342960, baseEnd_3342960] using wordTrace_append hprefix tailTrace_3342960
  have hstable : (prefixWord ++ tailWord_3342960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342960).length < 2 ^ (prefixWord ++ tailWord_3342960).sum := by decide
  have hdescent : baseEnd_3342960 < baseStart_3342960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342966 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_3342966 : Nat := 118140960795 + 3342966 * 2 ^ 59
def prefixEnd_3342966 : Nat := 4983230072969 + 3 ^ 40 * 3342966 * 2
def baseEnd_3342966 : Nat := 381455193252949525300219

theorem tailTrace_3342966 : CollatzResearch.WordTrace tailWord_3342966 prefixEnd_3342966 381455193252949525300219 := by
  unfold tailWord_3342966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620499175438286873975047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81285324538008393322400501 7620499175438286873975047)
  ·
    refine ⟨11430748763157430310962571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7620499175438286873975047 11430748763157430310962571)
    ·
      refine ⟨17146123144736145466443857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11430748763157430310962571 17146123144736145466443857)
      ·
        refine ⟨12859592358552109099832893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17146123144736145466443857 12859592358552109099832893)
        ·
          refine ⟨4822347134457040912437335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12859592358552109099832893 4822347134457040912437335)
          ·
            refine ⟨7233520701685561368656003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822347134457040912437335 7233520701685561368656003)
            ·
              refine ⟨10850281052528342052984005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233520701685561368656003 10850281052528342052984005)
              ·
                refine ⟨2034427697349064134934501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10850281052528342052984005 2034427697349064134934501)
                ·
                  refine ⟨381455193252949525300219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034427697349064134934501 381455193252949525300219)
                  ·
                    rfl

theorem cell22_3342966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_3342966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342966 prefixEnd_3342966 := by exact prefixLift 3342966
  have htrace : WordTrace (prefixWord ++ tailWord_3342966) baseStart_3342966 baseEnd_3342966 := by
    simpa [prefixWord, tailWord_3342966, baseEnd_3342966] using wordTrace_append hprefix tailTrace_3342966
  have hstable : (prefixWord ++ tailWord_3342966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342966).length < 2 ^ (prefixWord ++ tailWord_3342966).sum := by decide
  have hdescent : baseEnd_3342966 < baseStart_3342966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342994 : List Nat := [3, 2, 3, 1, 2, 2, 3, 6]
def baseStart_3342994 : Nat := 118140960795 + 3342994 * 2 ^ 59
def prefixEnd_3342994 : Nat := 4983230072969 + 3 ^ 40 * 3342994 * 2
def baseEnd_3342994 : Nat := 127152796081229537355619

theorem tailTrace_3342994 : CollatzResearch.WordTrace tailWord_3342994 prefixEnd_3342994 127152796081229537355619 := by
  unfold tailWord_3342994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30482252012727787691405009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81286005367274100510413357 30482252012727787691405009)
  ·
    refine ⟨22861689009545840768553757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30482252012727787691405009 22861689009545840768553757)
    ·
      refine ⟨8573133378579690288207659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22861689009545840768553757 8573133378579690288207659)
      ·
        refine ⟨12859700067869535432311489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573133378579690288207659 12859700067869535432311489)
        ·
          refine ⟨9644775050902151574233617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12859700067869535432311489 9644775050902151574233617)
          ·
            refine ⟨7233581288176613680675213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9644775050902151574233617 7233581288176613680675213)
            ·
              refine ⟨2712592983066230130253205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7233581288176613680675213 2712592983066230130253205)
              ·
                refine ⟨127152796081229537355619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2712592983066230130253205 127152796081229537355619)
                ·
                  rfl

theorem cell22_3342994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_3342994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342994 prefixEnd_3342994 := by exact prefixLift 3342994
  have htrace : WordTrace (prefixWord ++ tailWord_3342994) baseStart_3342994 baseEnd_3342994 := by
    simpa [prefixWord, tailWord_3342994, baseEnd_3342994] using wordTrace_append hprefix tailTrace_3342994
  have hstable : (prefixWord ++ tailWord_3342994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342994).length < 2 ^ (prefixWord ++ tailWord_3342994).sum := by decide
  have hdescent : baseEnd_3342994 < baseStart_3342994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342996 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3342996 : Nat := 118140960795 + 3342996 * 2 ^ 59
def prefixEnd_3342996 : Nat := 4983230072969 + 3 ^ 40 * 3342996 * 2
def baseEnd_3342996 : Nat := 1144375849371938497650565

theorem tailTrace_3342996 : CollatzResearch.WordTrace tailWord_3342996 prefixEnd_3342996 1144375849371938497650565 := by
  unfold tailWord_3342996
  simp only [CollatzResearch.WordTrace]
  refine ⟨60964540498451952553596421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81286053997935936738128561 60964540498451952553596421)
  ·
    refine ⟨11430851343459741103799329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60964540498451952553596421 11430851343459741103799329)
    ·
      refine ⟨8573138507594805827849497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11430851343459741103799329 8573138507594805827849497)
      ·
        refine ⟨6429853880696104370887123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8573138507594805827849497 6429853880696104370887123)
        ·
          refine ⟨9644780821044156556330685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6429853880696104370887123 9644780821044156556330685)
          ·
            refine ⟨3616792807891558708624007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9644780821044156556330685 3616792807891558708624007)
            ·
              refine ⟨5425189211837338062936011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616792807891558708624007 5425189211837338062936011)
              ·
                refine ⟨8137783817756007094404017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425189211837338062936011 8137783817756007094404017)
                ·
                  refine ⟨6103337863317005320803013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137783817756007094404017 6103337863317005320803013)
                  ·
                    refine ⟨1144375849371938497650565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6103337863317005320803013 1144375849371938497650565)
                    ·
                      rfl

theorem cell22_3342996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3342996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3342996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3342996 prefixEnd_3342996 := by exact prefixLift 3342996
  have htrace : WordTrace (prefixWord ++ tailWord_3342996) baseStart_3342996 baseEnd_3342996 := by
    simpa [prefixWord, tailWord_3342996, baseEnd_3342996] using wordTrace_append hprefix tailTrace_3342996
  have hstable : (prefixWord ++ tailWord_3342996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342996).length < 2 ^ (prefixWord ++ tailWord_3342996).sum := by decide
  have hdescent : baseEnd_3342996 < baseStart_3342996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343015 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3343015 : Nat := 118140960795 + 3343015 * 2 ^ 59
def prefixEnd_3343015 : Nat := 4983230072969 + 3 ^ 40 * 3343015 * 2
def baseEnd_3343015 : Nat := 1144382353460228781425507

theorem tailTrace_3343015 : CollatzResearch.WordTrace tailWord_3343015 prefixEnd_3343015 1144382353460228781425507 := by
  unfold tailWord_3343015
  simp only [CollatzResearch.WordTrace]
  refine ⟨121929773983835071352134499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81286515989223380901422999 121929773983835071352134499)
  ·
    refine ⟨182894660975752607028201749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121929773983835071352134499 182894660975752607028201749)
    ·
      refine ⟨8573187233238403454446957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182894660975752607028201749 8573187233238403454446957)
      ·
        refine ⟨3214945212464401295417609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8573187233238403454446957 3214945212464401295417609)
        ·
          refine ⟨2411208909348300971563207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214945212464401295417609 2411208909348300971563207)
          ·
            refine ⟨3616813364022451457344811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411208909348300971563207 3616813364022451457344811)
            ·
              refine ⟨5425220046033677186017217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616813364022451457344811 5425220046033677186017217)
              ·
                refine ⟨4068915034525257889512913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425220046033677186017217 4068915034525257889512913)
                ·
                  refine ⟨3051686275893943417134685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4068915034525257889512913 3051686275893943417134685)
                  ·
                    refine ⟨1144382353460228781425507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051686275893943417134685 1144382353460228781425507)
                    ·
                      rfl

theorem cell22_3343015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3343015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343015 prefixEnd_3343015 := by exact prefixLift 3343015
  have htrace : WordTrace (prefixWord ++ tailWord_3343015) baseStart_3343015 baseEnd_3343015 := by
    simpa [prefixWord, tailWord_3343015, baseEnd_3343015] using wordTrace_append hprefix tailTrace_3343015
  have hstable : (prefixWord ++ tailWord_3343015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343015).length < 2 ^ (prefixWord ++ tailWord_3343015).sum := by decide
  have hdescent : baseEnd_3343015 < baseStart_3343015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
