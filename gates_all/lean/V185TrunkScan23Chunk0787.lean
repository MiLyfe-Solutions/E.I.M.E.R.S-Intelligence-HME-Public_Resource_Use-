import V185TrunkScan23Chunk0786

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4655353 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_4655353 : Nat := 118140960795 + 4655353 * 2 ^ 59
def prefixEnd_4655353 : Nat := 4983230072969 + 3 ^ 40 * 4655353 * 2
def baseEnd_4655353 : Nat := 2390433705350429643677927

theorem tailTrace_4655353 : CollatzResearch.WordTrace tailWord_4655353 prefixEnd_4655353 2390433705350429643677927 := by
  unfold tailWord_4655353
  simp only [CollatzResearch.WordTrace]
  refine ⟨169794673103458626838674713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113196448735639084559116475 169794673103458626838674713)
  ·
    refine ⟨127346004827593970129006035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169794673103458626838674713 127346004827593970129006035)
    ·
      refine ⟨191019007241390955193509053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127346004827593970129006035 191019007241390955193509053)
      ·
        refine ⟨71632127715521608197565895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191019007241390955193509053 71632127715521608197565895)
        ·
          refine ⟨107448191573282412296348843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71632127715521608197565895 107448191573282412296348843)
          ·
            refine ⟨161172287359923618444523265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107448191573282412296348843 161172287359923618444523265)
            ·
              refine ⟨120879215519942713833392449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161172287359923618444523265 120879215519942713833392449)
              ·
                refine ⟨90659411639957035375044337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120879215519942713833392449 90659411639957035375044337)
                ·
                  refine ⟨67994558729967776531283253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90659411639957035375044337 67994558729967776531283253)
                  ·
                    refine ⟨6374489880934479049807805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67994558729967776531283253 6374489880934479049807805)
                    ·
                      refine ⟨2390433705350429643677927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6374489880934479049807805 2390433705350429643677927)
                      ·
                        rfl

theorem cell23_4655353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_4655353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655353 prefixEnd_4655353 := by exact prefixLift 4655353
  have htrace : WordTrace (prefixWord ++ tailWord_4655353) baseStart_4655353 baseEnd_4655353 := by
    simpa [prefixWord, tailWord_4655353, baseEnd_4655353] using wordTrace_append hprefix tailTrace_4655353
  have hstable : (prefixWord ++ tailWord_4655353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655353).length < 2 ^ (prefixWord ++ tailWord_4655353).sum := by decide
  have hdescent : baseEnd_4655353 < baseStart_4655353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655360 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 6]
def baseStart_4655360 : Nat := 118140960795 + 4655360 * 2 ^ 59
def prefixEnd_4655360 : Nat := 4983230072969 + 3 ^ 40 * 4655360 * 2
def baseEnd_4655360 : Nat := 265604144412779012921155

theorem tailTrace_4655360 : CollatzResearch.WordTrace tailWord_4655360 prefixEnd_4655360 265604144412779012921155 := by
  unfold tailWord_4655360
  simp only [CollatzResearch.WordTrace]
  refine ⟨84897464207216633517089767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113196618942955511356119689 84897464207216633517089767)
  ·
    refine ⟨127346196310824950275634651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84897464207216633517089767 127346196310824950275634651)
    ·
      refine ⟨191019294466237425413451977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127346196310824950275634651 191019294466237425413451977)
      ·
        refine ⟨143264470849678069060088983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191019294466237425413451977 143264470849678069060088983)
        ·
          refine ⟨214896706274517103590133475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143264470849678069060088983 214896706274517103590133475)
          ·
            refine ⟨322345059411775655385200213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214896706274517103590133475 322345059411775655385200213)
            ·
              refine ⟨3777481164981745961545315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 322345059411775655385200213 3777481164981745961545315)
              ·
                refine ⟨5666221747472618942317973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777481164981745961545315 5666221747472618942317973)
                ·
                  refine ⟨265604144412779012921155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5666221747472618942317973 265604144412779012921155)
                  ·
                    rfl

theorem cell23_4655360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 6].length) (baseStart_4655360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655360 prefixEnd_4655360 := by exact prefixLift 4655360
  have htrace : WordTrace (prefixWord ++ tailWord_4655360) baseStart_4655360 baseEnd_4655360 := by
    simpa [prefixWord, tailWord_4655360, baseEnd_4655360] using wordTrace_append hprefix tailTrace_4655360
  have hstable : (prefixWord ++ tailWord_4655360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655360).length < 2 ^ (prefixWord ++ tailWord_4655360).sum := by decide
  have hdescent : baseEnd_4655360 < baseStart_4655360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655420 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_4655420 : Nat := 118140960795 + 4655420 * 2 ^ 59
def prefixEnd_4655420 : Nat := 4983230072969 + 3 ^ 40 * 4655420 * 2
def baseEnd_4655420 : Nat := 796822702851426960513373

theorem tailTrace_4655420 : CollatzResearch.WordTrace tailWord_4655420 prefixEnd_4655420 796822702851426960513373 := by
  unfold tailWord_4655420
  simp only [CollatzResearch.WordTrace]
  refine ⟨84898558397107948640681857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113198077862810598187575809 84898558397107948640681857)
  ·
    refine ⟨63673918797830961480511393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84898558397107948640681857 63673918797830961480511393)
    ·
      refine ⟨47755439098373221110383545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63673918797830961480511393 47755439098373221110383545)
      ·
        refine ⟨35816579323779915832787659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47755439098373221110383545 35816579323779915832787659)
        ·
          refine ⟨53724868985669873749181489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35816579323779915832787659 53724868985669873749181489)
          ·
            refine ⟨40293651739252405311886117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53724868985669873749181489 40293651739252405311886117)
            ·
              refine ⟨7555059701109825995978647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40293651739252405311886117 7555059701109825995978647)
              ·
                refine ⟨11332589551664738993967971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7555059701109825995978647 11332589551664738993967971)
                ·
                  refine ⟨16998884327497108490951957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11332589551664738993967971 16998884327497108490951957)
                  ·
                    refine ⟨796822702851426960513373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16998884327497108490951957 796822702851426960513373)
                    ·
                      rfl

theorem cell23_4655420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_4655420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655420 prefixEnd_4655420 := by exact prefixLift 4655420
  have htrace : WordTrace (prefixWord ++ tailWord_4655420) baseStart_4655420 baseEnd_4655420 := by
    simpa [prefixWord, tailWord_4655420, baseEnd_4655420] using wordTrace_append hprefix tailTrace_4655420
  have hstable : (prefixWord ++ tailWord_4655420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655420).length < 2 ^ (prefixWord ++ tailWord_4655420).sum := by decide
  have hdescent : baseEnd_4655420 < baseStart_4655420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655427 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 5, 2, 2]
def baseStart_4655427 : Nat := 118140960795 + 4655427 * 2 ^ 59
def prefixEnd_4655427 : Nat := 4983230072969 + 3 ^ 40 * 4655427 * 2
def baseEnd_4655427 : Nat := 2390471702918862354152587

theorem tailTrace_4655427 : CollatzResearch.WordTrace tailWord_4655427 prefixEnd_4655427 2390471702918862354152587 := by
  unfold tailWord_4655427
  simp only [CollatzResearch.WordTrace]
  refine ⟨169797372105190537476868535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113198248070127024984579023 169797372105190537476868535)
  ·
    refine ⟨254696058157785806215302803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169797372105190537476868535 254696058157785806215302803)
    ·
      refine ⟨382044087236678709322954205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254696058157785806215302803 382044087236678709322954205)
      ·
        refine ⟨143266532713754515996107827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382044087236678709322954205 143266532713754515996107827)
        ·
          refine ⟨214899799070631773994161741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143266532713754515996107827 214899799070631773994161741)
          ·
            refine ⟨80587424651486915247810653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214899799070631773994161741 80587424651486915247810653)
            ·
              refine ⟨30220284244307593217928995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80587424651486915247810653 30220284244307593217928995)
              ·
                refine ⟨45330426366461389826893493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30220284244307593217928995 45330426366461389826893493)
                ·
                  refine ⟨4249727471855755296271265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45330426366461389826893493 4249727471855755296271265)
                  ·
                    refine ⟨3187295603891816472203449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4249727471855755296271265 3187295603891816472203449)
                    ·
                      refine ⟨2390471702918862354152587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187295603891816472203449 2390471702918862354152587)
                      ·
                        rfl

theorem cell23_4655427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_4655427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655427 prefixEnd_4655427 := by exact prefixLift 4655427
  have htrace : WordTrace (prefixWord ++ tailWord_4655427) baseStart_4655427 baseEnd_4655427 := by
    simpa [prefixWord, tailWord_4655427, baseEnd_4655427] using wordTrace_append hprefix tailTrace_4655427
  have hstable : (prefixWord ++ tailWord_4655427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655427).length < 2 ^ (prefixWord ++ tailWord_4655427).sum := by decide
  have hdescent : baseEnd_4655427 < baseStart_4655427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655440 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_4655440 : Nat := 118140960795 + 4655440 * 2 ^ 59
def prefixEnd_4655440 : Nat := 4983230072969 + 3 ^ 40 * 4655440 * 2
def baseEnd_4655440 : Nat := 2390478378167370803290027

theorem tailTrace_4655440 : CollatzResearch.WordTrace tailWord_4655440 prefixEnd_4655440 2390478378167370803290027 := by
  unfold tailWord_4655440
  simp only [CollatzResearch.WordTrace]
  refine ⟨84898923127071720348545887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113198564169428960464727849 84898923127071720348545887)
  ·
    refine ⟨127348384690607580522818831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84898923127071720348545887 127348384690607580522818831)
    ·
      refine ⟨191022577035911370784228247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127348384690607580522818831 191022577035911370784228247)
      ·
        refine ⟨286533865553867056176342371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191022577035911370784228247 286533865553867056176342371)
        ·
          refine ⟨429800798330800584264513557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286533865553867056176342371 429800798330800584264513557)
          ·
            refine ⟨20146912421756277387399073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 429800798330800584264513557 20146912421756277387399073)
            ·
              refine ⟨15110184316317208040549305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20146912421756277387399073 15110184316317208040549305)
              ·
                refine ⟨11332638237237906030411979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15110184316317208040549305 11332638237237906030411979)
                ·
                  refine ⟨16998957355856859045617969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11332638237237906030411979 16998957355856859045617969)
                  ·
                    refine ⟨12749218016892644284213477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16998957355856859045617969 12749218016892644284213477)
                    ·
                      refine ⟨2390478378167370803290027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12749218016892644284213477 2390478378167370803290027)
                      ·
                        rfl

theorem cell23_4655440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_4655440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655440 prefixEnd_4655440 := by exact prefixLift 4655440
  have htrace : WordTrace (prefixWord ++ tailWord_4655440) baseStart_4655440 baseEnd_4655440 := by
    simpa [prefixWord, tailWord_4655440, baseEnd_4655440] using wordTrace_append hprefix tailTrace_4655440
  have hstable : (prefixWord ++ tailWord_4655440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655440).length < 2 ^ (prefixWord ++ tailWord_4655440).sum := by decide
  have hdescent : baseEnd_4655440 < baseStart_4655440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655444 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_4655444 : Nat := 118140960795 + 4655444 * 2 ^ 59
def prefixEnd_4655444 : Nat := 4983230072969 + 3 ^ 40 * 4655444 * 2
def baseEnd_4655444 : Nat := 2390480432089988787640009

theorem tailTrace_4655444 : CollatzResearch.WordTrace tailWord_4655444 prefixEnd_4655444 2390480432089988787640009 := by
  unfold tailWord_4655444
  simp only [CollatzResearch.WordTrace]
  refine ⟨84898996073064474690118693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113198661430752632920158257 84898996073064474690118693)
  ·
    refine ⟨15918561763699589004397255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84898996073064474690118693 15918561763699589004397255)
    ·
      refine ⟨23877842645549383506595883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15918561763699589004397255 23877842645549383506595883)
      ·
        refine ⟨35816763968324075259893825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23877842645549383506595883 35816763968324075259893825)
        ·
          refine ⟨26862572976243056444920369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35816763968324075259893825 26862572976243056444920369)
          ·
            refine ⟨20146929732182292333690277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26862572976243056444920369 20146929732182292333690277)
            ·
              refine ⟨3777549324784179812566927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20146929732182292333690277 3777549324784179812566927)
              ·
                refine ⟨5666323987176269718850391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777549324784179812566927 5666323987176269718850391)
                ·
                  refine ⟨8499485980764404578275587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5666323987176269718850391 8499485980764404578275587)
                  ·
                    refine ⟨12749228971146606867413381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8499485980764404578275587 12749228971146606867413381)
                    ·
                      refine ⟨2390480432089988787640009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12749228971146606867413381 2390480432089988787640009)
                      ·
                        rfl

theorem cell23_4655444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_4655444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655444 prefixEnd_4655444 := by exact prefixLift 4655444
  have htrace : WordTrace (prefixWord ++ tailWord_4655444) baseStart_4655444 baseEnd_4655444 := by
    simpa [prefixWord, tailWord_4655444, baseEnd_4655444] using wordTrace_append hprefix tailTrace_4655444
  have hstable : (prefixWord ++ tailWord_4655444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655444).length < 2 ^ (prefixWord ++ tailWord_4655444).sum := by decide
  have hdescent : baseEnd_4655444 < baseStart_4655444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655447 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_4655447 : Nat := 118140960795 + 4655447 * 2 ^ 59
def prefixEnd_4655447 : Nat := 4983230072969 + 3 ^ 40 * 4655447 * 2
def baseEnd_4655447 : Nat := 2390481972531952275902495

theorem tailTrace_4655447 : CollatzResearch.WordTrace tailWord_4655447 prefixEnd_4655447 2390481972531952275902495 := by
  unfold tailWord_4655447
  simp only [CollatzResearch.WordTrace]
  refine ⟨169798101565118080892596595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113198734376745387261731063 169798101565118080892596595)
  ·
    refine ⟨254697152347677121338894893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169798101565118080892596595 254697152347677121338894893)
    ·
      refine ⟨95511432130378920502085585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254697152347677121338894893 95511432130378920502085585)
      ·
        refine ⟨71633574097784190376564189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95511432130378920502085585 71633574097784190376564189)
        ·
          refine ⟨26862590286669071391211571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71633574097784190376564189 26862590286669071391211571)
          ·
            refine ⟨40293885430003607086817357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26862590286669071391211571 40293885430003607086817357)
            ·
              refine ⟨15110207036251352657556509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40293885430003607086817357 15110207036251352657556509)
              ·
                refine ⟨5666327638594257246583691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15110207036251352657556509 5666327638594257246583691)
                ·
                  refine ⟨8499491457891385869875537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5666327638594257246583691 8499491457891385869875537)
                  ·
                    refine ⟨6374618593418539402406653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8499491457891385869875537 6374618593418539402406653)
                    ·
                      refine ⟨2390481972531952275902495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6374618593418539402406653 2390481972531952275902495)
                      ·
                        rfl

theorem cell23_4655447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_4655447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655447 prefixEnd_4655447 := by exact prefixLift 4655447
  have htrace : WordTrace (prefixWord ++ tailWord_4655447) baseStart_4655447 baseEnd_4655447 := by
    simpa [prefixWord, tailWord_4655447, baseEnd_4655447] using wordTrace_append hprefix tailTrace_4655447
  have hstable : (prefixWord ++ tailWord_4655447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655447).length < 2 ^ (prefixWord ++ tailWord_4655447).sum := by decide
  have hdescent : baseEnd_4655447 < baseStart_4655447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655461 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 1, 2, 2]
def baseStart_4655461 : Nat := 118140960795 + 4655461 * 2 ^ 59
def prefixEnd_4655461 : Nat := 4983230072969 + 3 ^ 40 * 4655461 * 2
def baseEnd_4655461 : Nat := 2390489161261115221127431

theorem tailTrace_4655461 : CollatzResearch.WordTrace tailWord_4655461 prefixEnd_4655461 2390489161261115221127431 := by
  unfold tailWord_4655461
  simp only [CollatzResearch.WordTrace]
  refine ⟨169798612187067361283606237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113199074791378240855737491 169798612187067361283606237)
  ·
    refine ⟨63674479570150260481352339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169798612187067361283606237 63674479570150260481352339)
    ·
      refine ⟨95511719355225390722028509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63674479570150260481352339 95511719355225390722028509)
      ·
        refine ⟨35816894758209521520760691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95511719355225390722028509 35816894758209521520760691)
        ·
          refine ⟨53725342137314282281141037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35816894758209521520760691 53725342137314282281141037)
          ·
            refine ⟨20147003301492855855427889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53725342137314282281141037 20147003301492855855427889)
            ·
              refine ⟨15110252476119641891570917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20147003301492855855427889 15110252476119641891570917)
              ·
                refine ⟨2833172339272432854669547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15110252476119641891570917 2833172339272432854669547)
                ·
                  refine ⟨4249758508908649282004321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833172339272432854669547 4249758508908649282004321)
                  ·
                    refine ⟨3187318881681486961503241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4249758508908649282004321 3187318881681486961503241)
                    ·
                      refine ⟨2390489161261115221127431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187318881681486961503241 2390489161261115221127431)
                      ·
                        rfl

theorem cell23_4655461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_4655461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655461 prefixEnd_4655461 := by exact prefixLift 4655461
  have htrace : WordTrace (prefixWord ++ tailWord_4655461) baseStart_4655461 baseEnd_4655461 := by
    simpa [prefixWord, tailWord_4655461, baseEnd_4655461] using wordTrace_append hprefix tailTrace_4655461
  have hstable : (prefixWord ++ tailWord_4655461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655461).length < 2 ^ (prefixWord ++ tailWord_4655461).sum := by decide
  have hdescent : baseEnd_4655461 < baseStart_4655461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655528 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4655528 : Nat := 118140960795 + 4655528 * 2 ^ 59
def prefixEnd_4655528 : Nat := 4983230072969 + 3 ^ 40 * 4655528 * 2
def baseEnd_4655528 : Nat := 2390523564464966458989623

theorem tailTrace_4655528 : CollatzResearch.WordTrace tailWord_4655528 prefixEnd_4655528 2390523564464966458989623 := by
  unfold tailWord_4655528
  simp only [CollatzResearch.WordTrace]
  refine ⟨84900527938912315863147619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113200703918549754484196825 84900527938912315863147619)
  ·
    refine ⟨127350791908368473794721429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84900527938912315863147619 127350791908368473794721429)
    ·
      refine ⟨5969568370704772209127567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127350791908368473794721429 5969568370704772209127567)
      ·
        refine ⟨8954352556057158313691351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969568370704772209127567 8954352556057158313691351)
        ·
          refine ⟨13431528834085737470537027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8954352556057158313691351 13431528834085737470537027)
          ·
            refine ⟨20147293251128606205805541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13431528834085737470537027 20147293251128606205805541)
            ·
              refine ⟨3777617484586613663588539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20147293251128606205805541 3777617484586613663588539)
              ·
                refine ⟨5666426226879920495382809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777617484586613663588539 5666426226879920495382809)
                ·
                  refine ⟨4249819670159940371537107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5666426226879920495382809 4249819670159940371537107)
                  ·
                    refine ⟨6374729505239910557305661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4249819670159940371537107 6374729505239910557305661)
                    ·
                      refine ⟨2390523564464966458989623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6374729505239910557305661 2390523564464966458989623)
                      ·
                        rfl

theorem cell23_4655528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4655528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655528 prefixEnd_4655528 := by exact prefixLift 4655528
  have htrace : WordTrace (prefixWord ++ tailWord_4655528) baseStart_4655528 baseEnd_4655528 := by
    simpa [prefixWord, tailWord_4655528, baseEnd_4655528] using wordTrace_append hprefix tailTrace_4655528
  have hstable : (prefixWord ++ tailWord_4655528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655528).length < 2 ^ (prefixWord ++ tailWord_4655528).sum := by decide
  have hdescent : baseEnd_4655528 < baseStart_4655528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655577 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 7, 2]
def baseStart_4655577 : Nat := 118140960795 + 4655577 * 2 ^ 59
def prefixEnd_4655577 : Nat := 4983230072969 + 3 ^ 40 * 4655577 * 2
def baseEnd_4655577 : Nat := 2390548725017036767276897

theorem tailTrace_4655577 : CollatzResearch.WordTrace tailWord_4655577 prefixEnd_4655577 2390548725017036767276897 := by
  unfold tailWord_4655577
  simp only [CollatzResearch.WordTrace]
  refine ⟨169802843054647113094828985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113201895369764742063219323 169802843054647113094828985)
  ·
    refine ⟨127352132290985334821121739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169802843054647113094828985 127352132290985334821121739)
    ·
      refine ⟨191028198436478002231682609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127352132290985334821121739 191028198436478002231682609)
      ·
        refine ⟨143271148827358501673761957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191028198436478002231682609 143271148827358501673761957)
        ·
          refine ⟨26863340405129719063830367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143271148827358501673761957 26863340405129719063830367)
          ·
            refine ⟨40295010607694578595745551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26863340405129719063830367 40295010607694578595745551)
            ·
              refine ⟨60442515911541867893618327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40295010607694578595745551 60442515911541867893618327)
              ·
                refine ⟨90663773867312801840427491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60442515911541867893618327 90663773867312801840427491)
                ·
                  refine ⟨135995660800969202760641237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90663773867312801840427491 135995660800969202760641237)
                  ·
                    refine ⟨3187398300022715689702529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135995660800969202760641237 3187398300022715689702529)
                    ·
                      refine ⟨2390548725017036767276897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187398300022715689702529 2390548725017036767276897)
                      ·
                        rfl

theorem cell23_4655577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_4655577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655577 prefixEnd_4655577 := by exact prefixLift 4655577
  have htrace : WordTrace (prefixWord ++ tailWord_4655577) baseStart_4655577 baseEnd_4655577 := by
    simpa [prefixWord, tailWord_4655577, baseEnd_4655577] using wordTrace_append hprefix tailTrace_4655577
  have hstable : (prefixWord ++ tailWord_4655577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655577).length < 2 ^ (prefixWord ++ tailWord_4655577).sum := by decide
  have hdescent : baseEnd_4655577 < baseStart_4655577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655610 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_4655610 : Nat := 118140960795 + 4655610 * 2 ^ 59
def prefixEnd_4655610 : Nat := 4983230072969 + 3 ^ 40 * 4655610 * 2
def baseEnd_4655610 : Nat := 2390565669878635138164245

theorem tailTrace_4655610 : CollatzResearch.WordTrace tailWord_4655610 prefixEnd_4655610 2390565669878635138164245 := by
  unfold tailWord_4655610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42451011665881889932695071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113202697775685039820520189 42451011665881889932695071)
  ·
    refine ⟨63676517498822834899042607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42451011665881889932695071 63676517498822834899042607)
    ·
      refine ⟨95514776248234252348563911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63676517498822834899042607 95514776248234252348563911)
      ·
        refine ⟨143272164372351378522845867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95514776248234252348563911 143272164372351378522845867)
        ·
          refine ⟨214908246558527067784268801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143272164372351378522845867 214908246558527067784268801)
          ·
            refine ⟨161181184918895300838201601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214908246558527067784268801 161181184918895300838201601)
            ·
              refine ⟨120885888689171475628651201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161181184918895300838201601 120885888689171475628651201)
              ·
                refine ⟨90664416516878606721488401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120885888689171475628651201 90664416516878606721488401)
                ·
                  refine ⟨67998312387658955041116301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90664416516878606721488401 67998312387658955041116301)
                  ·
                    refine ⟨25499367145372108140418613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67998312387658955041116301 25499367145372108140418613)
                    ·
                      refine ⟨2390565669878635138164245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25499367145372108140418613 2390565669878635138164245)
                      ·
                        rfl

theorem cell23_4655610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_4655610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655610 prefixEnd_4655610 := by exact prefixLift 4655610
  have htrace : WordTrace (prefixWord ++ tailWord_4655610) baseStart_4655610 baseEnd_4655610 := by
    simpa [prefixWord, tailWord_4655610, baseEnd_4655610] using wordTrace_append hprefix tailTrace_4655610
  have hstable : (prefixWord ++ tailWord_4655610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655610).length < 2 ^ (prefixWord ++ tailWord_4655610).sum := by decide
  have hdescent : baseEnd_4655610 < baseStart_4655610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655660 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_4655660 : Nat := 118140960795 + 4655660 * 2 ^ 59
def prefixEnd_4655660 : Nat := 4983230072969 + 3 ^ 40 * 4655660 * 2
def baseEnd_4655660 : Nat := 796863781303786647513005

theorem tailTrace_4655660 : CollatzResearch.WordTrace tailWord_4655660 prefixEnd_4655660 796863781303786647513005 := by
  unfold tailWord_4655660
  simp only [CollatzResearch.WordTrace]
  refine ⟨84902935156673209135050217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113203913542230945513400289 84902935156673209135050217)
  ·
    refine ⟨63677201367504906851287663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84902935156673209135050217 63677201367504906851287663)
    ·
      refine ⟨95515802051257360276931495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63677201367504906851287663 95515802051257360276931495)
      ·
        refine ⟨143273703076886040415397243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95515802051257360276931495 143273703076886040415397243)
        ·
          refine ⟨214910554615329060623095865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143273703076886040415397243 214910554615329060623095865)
          ·
            refine ⟨161182915961496795467321899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214910554615329060623095865 161182915961496795467321899)
            ·
              refine ⟨241774373942245193200982849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161182915961496795467321899 241774373942245193200982849)
              ·
                refine ⟨181330780456683894900737137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241774373942245193200982849 181330780456683894900737137)
                ·
                  refine ⟨135998085342512921175552853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181330780456683894900737137 135998085342512921175552853)
                  ·
                    refine ⟨796863781303786647513005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135998085342512921175552853 796863781303786647513005)
                    ·
                      rfl

theorem cell23_4655660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_4655660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655660 prefixEnd_4655660 := by exact prefixLift 4655660
  have htrace : WordTrace (prefixWord ++ tailWord_4655660) baseStart_4655660 baseEnd_4655660 := by
    simpa [prefixWord, tailWord_4655660, baseEnd_4655660] using wordTrace_append hprefix tailTrace_4655660
  have hstable : (prefixWord ++ tailWord_4655660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655660).length < 2 ^ (prefixWord ++ tailWord_4655660).sum := by decide
  have hdescent : baseEnd_4655660 < baseStart_4655660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655678 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4655678 : Nat := 118140960795 + 4655678 * 2 ^ 59
def prefixEnd_4655678 : Nat := 4983230072969 + 3 ^ 40 * 4655678 * 2
def baseEnd_4655678 : Nat := 2390600586563140872113933

theorem tailTrace_4655678 : CollatzResearch.WordTrace tailWord_4655678 prefixEnd_4655678 2390600586563140872113933 := by
  unfold tailWord_4655678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21225815853410150918031961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113204351218187471562837125 21225815853410150918031961)
  ·
    refine ⟨15919361890057613188523971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21225815853410150918031961 15919361890057613188523971)
    ·
      refine ⟨23879042835086419782785957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15919361890057613188523971 23879042835086419782785957)
      ·
        refine ⟨4477320531578703709272367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23879042835086419782785957 4477320531578703709272367)
        ·
          refine ⟨6715980797368055563908551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477320531578703709272367 6715980797368055563908551)
          ·
            refine ⟨10073971196052083345862827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715980797368055563908551 10073971196052083345862827)
            ·
              refine ⟨15110956794078125018794241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10073971196052083345862827 15110956794078125018794241)
              ·
                refine ⟨11333217595558593764095681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15110956794078125018794241 11333217595558593764095681)
                ·
                  refine ⟨8499913196668945323071761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11333217595558593764095681 8499913196668945323071761)
                  ·
                    refine ⟨6374934897501708992303821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8499913196668945323071761 6374934897501708992303821)
                    ·
                      refine ⟨2390600586563140872113933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6374934897501708992303821 2390600586563140872113933)
                      ·
                        rfl

theorem cell23_4655678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4655678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655678 prefixEnd_4655678 := by exact prefixLift 4655678
  have htrace : WordTrace (prefixWord ++ tailWord_4655678) baseStart_4655678 baseEnd_4655678 := by
    simpa [prefixWord, tailWord_4655678, baseEnd_4655678] using wordTrace_append hprefix tailTrace_4655678
  have hstable : (prefixWord ++ tailWord_4655678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655678).length < 2 ^ (prefixWord ++ tailWord_4655678).sum := by decide
  have hdescent : baseEnd_4655678 < baseStart_4655678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655691 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 1, 1, 3]
def baseStart_4655691 : Nat := 118140960795 + 4655691 * 2 ^ 59
def prefixEnd_4655691 : Nat := 4983230072969 + 3 ^ 40 * 4655691 * 2
def baseEnd_4655691 : Nat := 2390607261811649321251373

theorem tailTrace_4655691 : CollatzResearch.WordTrace tailWord_4655691 prefixEnd_4655691 2390607261811649321251373 := by
  unfold tailWord_4655691
  simp only [CollatzResearch.WordTrace]
  refine ⟨169807000976234110564478927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113204667317489407042985951 169807000976234110564478927)
  ·
    refine ⟨254710501464351165846718391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169807000976234110564478927 254710501464351165846718391)
    ·
      refine ⟨382065752196526748770077587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254710501464351165846718391 382065752196526748770077587)
      ·
        refine ⟨573098628294790123155116381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382065752196526748770077587 573098628294790123155116381)
        ·
          refine ⟨214911985610546296183168643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573098628294790123155116381 214911985610546296183168643)
          ·
            refine ⟨322367978415819444274752965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214911985610546296183168643 322367978415819444274752965)
            ·
              refine ⟨60443995952966145801516181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 322367978415819444274752965 60443995952966145801516181)
              ·
                refine ⟨2833312310295288084446071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60443995952966145801516181 2833312310295288084446071)
                ·
                  refine ⟨4249968465442932126669107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833312310295288084446071 4249968465442932126669107)
                  ·
                    refine ⟨6374952698164398190003661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4249968465442932126669107 6374952698164398190003661)
                    ·
                      refine ⟨2390607261811649321251373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6374952698164398190003661 2390607261811649321251373)
                      ·
                        rfl

theorem cell23_4655691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 1, 3].length) (baseStart_4655691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655691 prefixEnd_4655691 := by exact prefixLift 4655691
  have htrace : WordTrace (prefixWord ++ tailWord_4655691) baseStart_4655691 baseEnd_4655691 := by
    simpa [prefixWord, tailWord_4655691, baseEnd_4655691] using wordTrace_append hprefix tailTrace_4655691
  have hstable : (prefixWord ++ tailWord_4655691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655691).length < 2 ^ (prefixWord ++ tailWord_4655691).sum := by decide
  have hdescent : baseEnd_4655691 < baseStart_4655691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655727 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_4655727 : Nat := 118140960795 + 4655727 * 2 ^ 59
def prefixEnd_4655727 : Nat := 4983230072969 + 3 ^ 40 * 4655727 * 2
def baseEnd_4655727 : Nat := 2390625747115211180401207

theorem tailTrace_4655727 : CollatzResearch.WordTrace tailWord_4655727 prefixEnd_4655727 2390625747115211180401207 := by
  unfold tailWord_4655727
  simp only [CollatzResearch.WordTrace]
  refine ⟨169808314004103688712789435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113205542669402459141859623 169808314004103688712789435)
  ·
    refine ⟨254712471006155533069184153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169808314004103688712789435 254712471006155533069184153)
    ·
      refine ⟨191034353254616649801888115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254712471006155533069184153 191034353254616649801888115)
      ·
        refine ⟨286551529881924974702832173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191034353254616649801888115 286551529881924974702832173)
        ·
          refine ⟨107456823705721865513562065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286551529881924974702832173 107456823705721865513562065)
          ·
            refine ⟨80592617779291399135171549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107456823705721865513562065 80592617779291399135171549)
            ·
              refine ⟨30222231667234274675689331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80592617779291399135171549 30222231667234274675689331)
              ·
                refine ⟨45333347500851412013533997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30222231667234274675689331 45333347500851412013533997)
                ·
                  refine ⟨17000005312819279505075249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45333347500851412013533997 17000005312819279505075249)
                  ·
                    refine ⟨12750003984614459628806437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17000005312819279505075249 12750003984614459628806437)
                    ·
                      refine ⟨2390625747115211180401207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12750003984614459628806437 2390625747115211180401207)
                      ·
                        rfl

theorem cell23_4655727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_4655727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655727 prefixEnd_4655727 := by exact prefixLift 4655727
  have htrace : WordTrace (prefixWord ++ tailWord_4655727) baseStart_4655727 baseEnd_4655727 := by
    simpa [prefixWord, tailWord_4655727, baseEnd_4655727] using wordTrace_append hprefix tailTrace_4655727
  have hstable : (prefixWord ++ tailWord_4655727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655727).length < 2 ^ (prefixWord ++ tailWord_4655727).sum := by decide
  have hdescent : baseEnd_4655727 < baseStart_4655727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655767 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 2, 7]
def baseStart_4655767 : Nat := 118140960795 + 4655767 * 2 ^ 59
def prefixEnd_4655767 : Nat := 4983230072969 + 3 ^ 40 * 4655767 * 2
def baseEnd_4655767 : Nat := 796882095447130341300341

theorem tailTrace_4655767 : CollatzResearch.WordTrace tailWord_4655767 prefixEnd_4655767 796882095447130341300341 := by
  unfold tailWord_4655767
  simp only [CollatzResearch.WordTrace]
  refine ⟨169809772923958775544245555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113206515282639183696163703 169809772923958775544245555)
  ·
    refine ⟨254714659385938163316368333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169809772923958775544245555 254714659385938163316368333)
    ·
      refine ⟨95517997269726811243638125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254714659385938163316368333 95517997269726811243638125)
      ·
        refine ⟨35819248976147554216364297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95517997269726811243638125 35819248976147554216364297)
        ·
          refine ⟨26864436732110665662273223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35819248976147554216364297 26864436732110665662273223)
          ·
            refine ⟨40296655098165998493409835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26864436732110665662273223 40296655098165998493409835)
            ·
              refine ⟨60444982647248997740114753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40296655098165998493409835 60444982647248997740114753)
              ·
                refine ⟨45333736985436748305086065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60444982647248997740114753 45333736985436748305086065)
                ·
                  refine ⟨34000302739077561228814549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45333736985436748305086065 34000302739077561228814549)
                  ·
                    refine ⟨796882095447130341300341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34000302739077561228814549 796882095447130341300341)
                    ·
                      rfl

theorem cell23_4655767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_4655767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655767 prefixEnd_4655767 := by exact prefixLift 4655767
  have htrace : WordTrace (prefixWord ++ tailWord_4655767) baseStart_4655767 baseEnd_4655767 := by
    simpa [prefixWord, tailWord_4655767, baseEnd_4655767] using wordTrace_append hprefix tailTrace_4655767
  have hstable : (prefixWord ++ tailWord_4655767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655767).length < 2 ^ (prefixWord ++ tailWord_4655767).sum := by decide
  have hdescent : baseEnd_4655767 < baseStart_4655767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655921 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 3, 4]
def baseStart_4655921 : Nat := 118140960795 + 4655921 * 2 ^ 59
def prefixEnd_4655921 : Nat := 4983230072969 + 3 ^ 40 * 4655921 * 2
def baseEnd_4655921 : Nat := 796908454120727807125105

theorem tailTrace_4655921 : CollatzResearch.WordTrace tailWord_4655921 prefixEnd_4655921 796908454120727807125105 := by
  unfold tailWord_4655921
  simp only [CollatzResearch.WordTrace]
  refine ⟨169815389765400859845351617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113210259843600573230234411 169815389765400859845351617)
  ·
    refine ⟨127361542324050644884013713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169815389765400859845351617 127361542324050644884013713)
    ·
      refine ⟨95521156743037983663010285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127361542324050644884013713 95521156743037983663010285)
      ·
        refine ⟨35820433778639243873628857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95521156743037983663010285 35820433778639243873628857)
        ·
          refine ⟨26865325333979432905221643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35820433778639243873628857 26865325333979432905221643)
          ·
            refine ⟨40297988000969149357832465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26865325333979432905221643 40297988000969149357832465)
            ·
              refine ⟨30223491000726862018374349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40297988000969149357832465 30223491000726862018374349)
              ·
                refine ⟨11333809125272573256890381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30223491000726862018374349 11333809125272573256890381)
                ·
                  refine ⟨4250178421977214971333893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11333809125272573256890381 4250178421977214971333893)
                  ·
                    refine ⟨796908454120727807125105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250178421977214971333893 796908454120727807125105)
                    ·
                      rfl

theorem cell23_4655921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_4655921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655921 prefixEnd_4655921 := by exact prefixLift 4655921
  have htrace : WordTrace (prefixWord ++ tailWord_4655921) baseStart_4655921 baseEnd_4655921 := by
    simpa [prefixWord, tailWord_4655921, baseEnd_4655921] using wordTrace_append hprefix tailTrace_4655921
  have hstable : (prefixWord ++ tailWord_4655921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655921).length < 2 ^ (prefixWord ++ tailWord_4655921).sum := by decide
  have hdescent : baseEnd_4655921 < baseStart_4655921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655942 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_4655942 : Nat := 118140960795 + 4655942 * 2 ^ 59
def prefixEnd_4655942 : Nat := 4983230072969 + 3 ^ 40 * 4655942 * 2
def baseEnd_4655942 : Nat := 796912048485309279737573

theorem tailTrace_4655942 : CollatzResearch.WordTrace tailWord_4655942 prefixEnd_4655942 796912048485309279737573 := by
  unfold tailWord_4655942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306754865572649388495815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113210770465549853621244053 5306754865572649388495815)
  ·
    refine ⟨7960132298358974082743723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5306754865572649388495815 7960132298358974082743723)
    ·
      refine ⟨11940198447538461124115585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7960132298358974082743723 11940198447538461124115585)
      ·
        refine ⟨8955148835653845843086689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11940198447538461124115585 8955148835653845843086689)
        ·
          refine ⟨6716361626740384382315017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8955148835653845843086689 6716361626740384382315017)
          ·
            refine ⟨5037271220055288286736263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6716361626740384382315017 5037271220055288286736263)
            ·
              refine ⟨7555906830082932430104395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5037271220055288286736263 7555906830082932430104395)
              ·
                refine ⟨11333860245124398645156593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7555906830082932430104395 11333860245124398645156593)
                ·
                  refine ⟨8500395183843298983867445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11333860245124398645156593 8500395183843298983867445)
                  ·
                    refine ⟨796912048485309279737573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8500395183843298983867445 796912048485309279737573)
                    ·
                      rfl

theorem cell23_4655942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_4655942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655942 prefixEnd_4655942 := by exact prefixLift 4655942
  have htrace : WordTrace (prefixWord ++ tailWord_4655942) baseStart_4655942 baseEnd_4655942 := by
    simpa [prefixWord, tailWord_4655942, baseEnd_4655942] using wordTrace_append hprefix tailTrace_4655942
  have hstable : (prefixWord ++ tailWord_4655942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655942).length < 2 ^ (prefixWord ++ tailWord_4655942).sum := by decide
  have hdescent : baseEnd_4655942 < baseStart_4655942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4655948 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_4655948 : Nat := 118140960795 + 4655948 * 2 ^ 59
def prefixEnd_4655948 : Nat := 4983230072969 + 3 ^ 40 * 4655948 * 2
def baseEnd_4655948 : Nat := 2390739226339854815737691

theorem tailTrace_4655948 : CollatzResearch.WordTrace tailWord_4655948 prefixEnd_4655948 2390739226339854815737691 := by
  unfold tailWord_4655948
  simp only [CollatzResearch.WordTrace]
  refine ⟨84908187268151521728292249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113210916357535362304389665 84908187268151521728292249)
  ·
    refine ⟨63681140451113641296219187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84908187268151521728292249 63681140451113641296219187)
    ·
      refine ⟨95521710676670461944328781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63681140451113641296219187 95521710676670461944328781)
      ·
        refine ⟨35820641503751423229123293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95521710676670461944328781 35820641503751423229123293)
        ·
          refine ⟨13432740563906783710921235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35820641503751423229123293 13432740563906783710921235)
          ·
            refine ⟨20149110845860175566381853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13432740563906783710921235 20149110845860175566381853)
            ·
              refine ⟨7555916567197565837393195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20149110845860175566381853 7555916567197565837393195)
              ·
                refine ⟨11333874850796348756089793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7555916567197565837393195 11333874850796348756089793)
                ·
                  refine ⟨8500406138097261567067345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11333874850796348756089793 8500406138097261567067345)
                  ·
                    refine ⟨6375304603572946175300509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8500406138097261567067345 6375304603572946175300509)
                    ·
                      refine ⟨2390739226339854815737691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6375304603572946175300509 2390739226339854815737691)
                      ·
                        rfl

theorem cell23_4655948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_4655948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4655948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4655948 prefixEnd_4655948 := by exact prefixLift 4655948
  have htrace : WordTrace (prefixWord ++ tailWord_4655948) baseStart_4655948 baseEnd_4655948 := by
    simpa [prefixWord, tailWord_4655948, baseEnd_4655948] using wordTrace_append hprefix tailTrace_4655948
  have hstable : (prefixWord ++ tailWord_4655948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4655948).length < 2 ^ (prefixWord ++ tailWord_4655948).sum := by decide
  have hdescent : baseEnd_4655948 < baseStart_4655948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4655948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656011 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 4, 4]
def baseStart_4656011 : Nat := 118140960795 + 4656011 * 2 ^ 59
def prefixEnd_4656011 : Nat := 4983230072969 + 3 ^ 40 * 4656011 * 2
def baseEnd_4656011 : Nat := 796923858540362689749967

theorem tailTrace_4656011 : CollatzResearch.WordTrace tailWord_4656011 prefixEnd_4656011 796923858540362689749967 := by
  unfold tailWord_4656011
  simp only [CollatzResearch.WordTrace]
  refine ⟨169818672335074805216127887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113212448223383203477418591 169818672335074805216127887)
  ·
    refine ⟨254728008502612207824191831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169818672335074805216127887 254728008502612207824191831)
    ·
      refine ⟨382092012753918311736287747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254728008502612207824191831 382092012753918311736287747)
      ·
        refine ⟨573138019130877467604431621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382092012753918311736287747 573138019130877467604431621)
        ·
          refine ⟨107463378587039525175830929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 573138019130877467604431621 107463378587039525175830929)
          ·
            refine ⟨80597533940279643881873197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107463378587039525175830929 80597533940279643881873197)
            ·
              refine ⟨30224075227604866455702449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80597533940279643881873197 30224075227604866455702449)
              ·
                refine ⟨22668056420703649841776837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30224075227604866455702449 22668056420703649841776837)
                ·
                  refine ⟨4250260578881934345333157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22668056420703649841776837 4250260578881934345333157)
                  ·
                    refine ⟨796923858540362689749967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250260578881934345333157 796923858540362689749967)
                    ·
                      rfl

theorem cell23_4656011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 4].length) (baseStart_4656011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656011 prefixEnd_4656011 := by exact prefixLift 4656011
  have htrace : WordTrace (prefixWord ++ tailWord_4656011) baseStart_4656011 baseEnd_4656011 := by
    simpa [prefixWord, tailWord_4656011, baseEnd_4656011] using wordTrace_append hprefix tailTrace_4656011
  have hstable : (prefixWord ++ tailWord_4656011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656011).length < 2 ^ (prefixWord ++ tailWord_4656011).sum := by decide
  have hdescent : baseEnd_4656011 < baseStart_4656011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656021 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_4656021 : Nat := 118140960795 + 4656021 * 2 ^ 59
def prefixEnd_4656021 : Nat := 4983230072969 + 3 ^ 40 * 4656021 * 2
def baseEnd_4656021 : Nat := 2390776710427633030124855

theorem tailTrace_4656021 : CollatzResearch.WordTrace tailWord_4656021 prefixEnd_4656021 2390776710427633030124855 := by
  unfold tailWord_4656021
  simp only [CollatzResearch.WordTrace]
  refine ⟨169819037065038576923991917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113212691376692384615994611 169819037065038576923991917)
  ·
    refine ⟨63682138899389466346496969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169819037065038576923991917 63682138899389466346496969)
    ·
      refine ⟨47761604174542099759872727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63682138899389466346496969 47761604174542099759872727)
      ·
        refine ⟨71642406261813149639809091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47761604174542099759872727 71642406261813149639809091)
        ·
          refine ⟨107463609392719724459713637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71642406261813149639809091 107463609392719724459713637)
          ·
            refine ⟨20149426761134948336196307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107463609392719724459713637 20149426761134948336196307)
            ·
              refine ⟨30224140141702422504294461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20149426761134948336196307 30224140141702422504294461)
              ·
                refine ⟨11334052553138408439110423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30224140141702422504294461 11334052553138408439110423)
                ·
                  refine ⟨17001078829707612658665635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11334052553138408439110423 17001078829707612658665635)
                  ·
                    refine ⟨25501618244561418987998453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17001078829707612658665635 25501618244561418987998453)
                    ·
                      refine ⟨2390776710427633030124855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25501618244561418987998453 2390776710427633030124855)
                      ·
                        rfl

theorem cell23_4656021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_4656021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656021 prefixEnd_4656021 := by exact prefixLift 4656021
  have htrace : WordTrace (prefixWord ++ tailWord_4656021) baseStart_4656021 baseEnd_4656021 := by
    simpa [prefixWord, tailWord_4656021, baseEnd_4656021] using wordTrace_append hprefix tailTrace_4656021
  have hstable : (prefixWord ++ tailWord_4656021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656021).length < 2 ^ (prefixWord ++ tailWord_4656021).sum := by decide
  have hdescent : baseEnd_4656021 < baseStart_4656021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656031 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4656031 : Nat := 118140960795 + 4656031 * 2 ^ 59
def prefixEnd_4656031 : Nat := 4983230072969 + 3 ^ 40 * 4656031 * 2
def baseEnd_4656031 : Nat := 2390781845234177990999809

theorem tailTrace_4656031 : CollatzResearch.WordTrace tailWord_4656031 prefixEnd_4656031 2390781845234177990999809 := by
  unfold tailWord_4656031
  simp only [CollatzResearch.WordTrace]
  refine ⟨169819401795002348631855947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113212934530001565754570631 169819401795002348631855947)
  ·
    refine ⟨254729102692503522947783921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169819401795002348631855947 254729102692503522947783921)
    ·
      refine ⟨191046827019377642210837941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254729102692503522947783921 191046827019377642210837941)
      ·
        refine ⟨17910640033066653957266057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191046827019377642210837941 17910640033066653957266057)
        ·
          refine ⟨13432980024799990467949543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17910640033066653957266057 13432980024799990467949543)
          ·
            refine ⟨20149470037199985701924315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13432980024799990467949543 20149470037199985701924315)
            ·
              refine ⟨30224205055799978552886473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20149470037199985701924315 30224205055799978552886473)
              ·
                refine ⟨22668153791849983914664855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30224205055799978552886473 22668153791849983914664855)
                ·
                  refine ⟨34002230687774975871997283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22668153791849983914664855 34002230687774975871997283)
                  ·
                    refine ⟨51003346031662463807995925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34002230687774975871997283 51003346031662463807995925)
                    ·
                      refine ⟨2390781845234177990999809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51003346031662463807995925 2390781845234177990999809)
                      ·
                        rfl

theorem cell23_4656031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4656031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656031 prefixEnd_4656031 := by exact prefixLift 4656031
  have htrace : WordTrace (prefixWord ++ tailWord_4656031) baseStart_4656031 baseEnd_4656031 := by
    simpa [prefixWord, tailWord_4656031, baseEnd_4656031] using wordTrace_append hprefix tailTrace_4656031
  have hstable : (prefixWord ++ tailWord_4656031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656031).length < 2 ^ (prefixWord ++ tailWord_4656031).sum := by decide
  have hdescent : baseEnd_4656031 < baseStart_4656031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656035 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 3, 2, 2]
def baseStart_4656035 : Nat := 118140960795 + 4656035 * 2 ^ 59
def prefixEnd_4656035 : Nat := 4983230072969 + 3 ^ 40 * 4656035 * 2
def baseEnd_4656035 : Nat := 2390783899156795975349791

theorem tailTrace_4656035 : CollatzResearch.WordTrace tailWord_4656035 prefixEnd_4656035 2390783899156795975349791 := by
  unfold tailWord_4656035
  simp only [CollatzResearch.WordTrace]
  refine ⟨169819547686987857315001559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113213031791325238210001039 169819547686987857315001559)
  ·
    refine ⟨254729321530481785972502339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169819547686987857315001559 254729321530481785972502339)
    ·
      refine ⟨382093982295722678958753509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254729321530481785972502339 382093982295722678958753509)
      ·
        refine ⟨71642621680448002304766283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382093982295722678958753509 71642621680448002304766283)
        ·
          refine ⟨107463932520672003457149425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71642621680448002304766283 107463932520672003457149425)
          ·
            refine ⟨80597949390504002592862069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107463932520672003457149425 80597949390504002592862069)
            ·
              refine ⟨7556057755359750243080819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80597949390504002592862069 7556057755359750243080819)
              ·
                refine ⟨11334086633039625364621229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7556057755359750243080819 11334086633039625364621229)
                ·
                  refine ⟨4250282487389859511732961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11334086633039625364621229 4250282487389859511732961)
                  ·
                    refine ⟨3187711865542394633799721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250282487389859511732961 3187711865542394633799721)
                    ·
                      refine ⟨2390783899156795975349791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187711865542394633799721 2390783899156795975349791)
                      ·
                        rfl

theorem cell23_4656035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_4656035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656035 prefixEnd_4656035 := by exact prefixLift 4656035
  have htrace : WordTrace (prefixWord ++ tailWord_4656035) baseStart_4656035 baseEnd_4656035 := by
    simpa [prefixWord, tailWord_4656035, baseEnd_4656035] using wordTrace_append hprefix tailTrace_4656035
  have hstable : (prefixWord ++ tailWord_4656035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656035).length < 2 ^ (prefixWord ++ tailWord_4656035).sum := by decide
  have hdescent : baseEnd_4656035 < baseStart_4656035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656052 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4656052 : Nat := 118140960795 + 4656052 * 2 ^ 59
def prefixEnd_4656052 : Nat := 4983230072969 + 3 ^ 40 * 4656052 * 2
def baseEnd_4656052 : Nat := 2390792628327922408837213

theorem tailTrace_4656052 : CollatzResearch.WordTrace tailWord_4656052 prefixEnd_4656052 2390792628327922408837213 := by
  unfold tailWord_4656052
  simp only [CollatzResearch.WordTrace]
  refine ⟨84910083863963134609185205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113213445151950846145580273 84910083863963134609185205)
  ·
    refine ⟨7960320362246543869611113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84910083863963134609185205 7960320362246543869611113)
    ·
      refine ⟨5970240271684907902208335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7960320362246543869611113 5970240271684907902208335)
      ·
        refine ⟨8955360407527361853312503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970240271684907902208335 8955360407527361853312503)
        ·
          refine ⟨13433040611291042779968755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8955360407527361853312503 13433040611291042779968755)
          ·
            refine ⟨20149560916936564169953133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13433040611291042779968755 20149560916936564169953133)
            ·
              refine ⟨7556085343851211563732425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20149560916936564169953133 7556085343851211563732425)
              ·
                refine ⟨5667064007888408672799319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7556085343851211563732425 5667064007888408672799319)
                ·
                  refine ⟨8500596011832613009198979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667064007888408672799319 8500596011832613009198979)
                  ·
                    refine ⟨12750894017748919513798469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8500596011832613009198979 12750894017748919513798469)
                    ·
                      refine ⟨2390792628327922408837213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12750894017748919513798469 2390792628327922408837213)
                      ·
                        rfl

theorem cell23_4656052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4656052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656052 prefixEnd_4656052 := by exact prefixLift 4656052
  have htrace : WordTrace (prefixWord ++ tailWord_4656052) baseStart_4656052 baseEnd_4656052 := by
    simpa [prefixWord, tailWord_4656052, baseEnd_4656052] using wordTrace_append hprefix tailTrace_4656052
  have hstable : (prefixWord ++ tailWord_4656052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656052).length < 2 ^ (prefixWord ++ tailWord_4656052).sum := by decide
  have hdescent : baseEnd_4656052 < baseStart_4656052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656072 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_4656072 : Nat := 118140960795 + 4656072 * 2 ^ 59
def prefixEnd_4656072 : Nat := 4983230072969 + 3 ^ 40 * 4656072 * 2
def baseEnd_4656072 : Nat := 2390802897941012330587121

theorem tailTrace_4656072 : CollatzResearch.WordTrace tailWord_4656072 prefixEnd_4656072 2390802897941012330587121 := by
  unfold tailWord_4656072
  simp only [CollatzResearch.WordTrace]
  refine ⟨84910448593926906317049235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113213931458569208422732313 84910448593926906317049235)
  ·
    refine ⟨127365672890890359475573853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84910448593926906317049235 127365672890890359475573853)
    ·
      refine ⟨47762127334083884803340195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127365672890890359475573853 47762127334083884803340195)
      ·
        refine ⟨71643191001125827205010293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47762127334083884803340195 71643191001125827205010293)
        ·
          refine ⟨6716549156355546300469715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71643191001125827205010293 6716549156355546300469715)
          ·
            refine ⟨10074823734533319450704573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6716549156355546300469715 10074823734533319450704573)
            ·
              refine ⟨3778058900449994794014215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10074823734533319450704573 3778058900449994794014215)
              ·
                refine ⟨5667088350674992191021323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778058900449994794014215 5667088350674992191021323)
                ·
                  refine ⟨8500632526012488286531985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667088350674992191021323 8500632526012488286531985)
                  ·
                    refine ⟨6375474394509366214898989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8500632526012488286531985 6375474394509366214898989)
                    ·
                      refine ⟨2390802897941012330587121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6375474394509366214898989 2390802897941012330587121)
                      ·
                        rfl

theorem cell23_4656072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_4656072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656072 prefixEnd_4656072 := by exact prefixLift 4656072
  have htrace : WordTrace (prefixWord ++ tailWord_4656072) baseStart_4656072 baseEnd_4656072 := by
    simpa [prefixWord, tailWord_4656072, baseEnd_4656072] using wordTrace_append hprefix tailTrace_4656072
  have hstable : (prefixWord ++ tailWord_4656072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656072).length < 2 ^ (prefixWord ++ tailWord_4656072).sum := by decide
  have hdescent : baseEnd_4656072 < baseStart_4656072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656086 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_4656086 : Nat := 118140960795 + 4656086 * 2 ^ 59
def prefixEnd_4656086 : Nat := 4983230072969 + 3 ^ 40 * 4656086 * 2
def baseEnd_4656086 : Nat := 2390810086670175275812057

theorem tailTrace_4656086 : CollatzResearch.WordTrace tailWord_4656086 prefixEnd_4656086 2390810086670175275812057 := by
  unfold tailWord_4656086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10613837988112693314069257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113214271873202062016738741 10613837988112693314069257)
  ·
    refine ⟨7960378491084519985551943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10613837988112693314069257 7960378491084519985551943)
    ·
      refine ⟨11940567736626779978327915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7960378491084519985551943 11940567736626779978327915)
      ·
        refine ⟨17910851604940169967491873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940567736626779978327915 17910851604940169967491873)
        ·
          refine ⟨13433138703705127475618905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17910851604940169967491873 13433138703705127475618905)
          ·
            refine ⟨10074854027778845606714179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13433138703705127475618905 10074854027778845606714179)
            ·
              refine ⟨15112281041668268410071269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10074854027778845606714179 15112281041668268410071269)
              ·
                refine ⟨2833552695312800326888363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15112281041668268410071269 2833552695312800326888363)
                ·
                  refine ⟨4250329042969200490332545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833552695312800326888363 4250329042969200490332545)
                  ·
                    refine ⟨3187746782226900367749409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250329042969200490332545 3187746782226900367749409)
                    ·
                      refine ⟨2390810086670175275812057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187746782226900367749409 2390810086670175275812057)
                      ·
                        rfl

theorem cell23_4656086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_4656086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656086 prefixEnd_4656086 := by exact prefixLift 4656086
  have htrace : WordTrace (prefixWord ++ tailWord_4656086) baseStart_4656086 baseEnd_4656086 := by
    simpa [prefixWord, tailWord_4656086, baseEnd_4656086] using wordTrace_append hprefix tailTrace_4656086
  have hstable : (prefixWord ++ tailWord_4656086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656086).length < 2 ^ (prefixWord ++ tailWord_4656086).sum := by decide
  have hdescent : baseEnd_4656086 < baseStart_4656086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656121 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_4656121 : Nat := 118140960795 + 4656121 * 2 ^ 59
def prefixEnd_4656121 : Nat := 4983230072969 + 3 ^ 40 * 4656121 * 2
def baseEnd_4656121 : Nat := 2390828058493082638874395

theorem tailTrace_4656121 : CollatzResearch.WordTrace tailWord_4656121 prefixEnd_4656121 2390828058493082638874395 := by
  unfold tailWord_4656121
  simp only [CollatzResearch.WordTrace]
  refine ⟨169822684364676294002632217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113215122909784196001754811 169822684364676294002632217)
  ·
    refine ⟨127367013273507220501974163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169822684364676294002632217 127367013273507220501974163)
    ·
      refine ⟨191050519910260830752961245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127367013273507220501974163 191050519910260830752961245)
      ·
        refine ⟨71643944966347811532360467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191050519910260830752961245 71643944966347811532360467)
        ·
          refine ⟨107465917449521717298540701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71643944966347811532360467 107465917449521717298540701)
          ·
            refine ⟨40299719043570643986952763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107465917449521717298540701 40299719043570643986952763)
            ·
              refine ⟨60449578565355965980429145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40299719043570643986952763 60449578565355965980429145)
              ·
                refine ⟨45337183924016974485321859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60449578565355965980429145 45337183924016974485321859)
                ·
                  refine ⟨68005775886025461727982789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45337183924016974485321859 68005775886025461727982789)
                  ·
                    refine ⟨12751082978629774073996773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68005775886025461727982789 12751082978629774073996773)
                    ·
                      refine ⟨2390828058493082638874395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12751082978629774073996773 2390828058493082638874395)
                      ·
                        rfl

theorem cell23_4656121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_4656121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656121 prefixEnd_4656121 := by exact prefixLift 4656121
  have htrace : WordTrace (prefixWord ++ tailWord_4656121) baseStart_4656121 baseEnd_4656121 := by
    simpa [prefixWord, tailWord_4656121, baseEnd_4656121] using wordTrace_append hprefix tailTrace_4656121
  have hstable : (prefixWord ++ tailWord_4656121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656121).length < 2 ^ (prefixWord ++ tailWord_4656121).sum := by decide
  have hdescent : baseEnd_4656121 < baseStart_4656121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656125 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_4656125 : Nat := 118140960795 + 4656125 * 2 ^ 59
def prefixEnd_4656125 : Nat := 4983230072969 + 3 ^ 40 * 4656125 * 2
def baseEnd_4656125 : Nat := 2390830112415700623224377

theorem tailTrace_4656125 : CollatzResearch.WordTrace tailWord_4656125 prefixEnd_4656125 2390830112415700623224377 := by
  unfold tailWord_4656125
  simp only [CollatzResearch.WordTrace]
  refine ⟨169822830256661802685777829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113215220171107868457185219 169822830256661802685777829)
  ·
    refine ⟨31841780673124088003583343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169822830256661802685777829 31841780673124088003583343)
    ·
      refine ⟨47762671009686132005375015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31841780673124088003583343 47762671009686132005375015)
      ·
        refine ⟨71644006514529198008062523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47762671009686132005375015 71644006514529198008062523)
        ·
          refine ⟨107466009771793797012093785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71644006514529198008062523 107466009771793797012093785)
          ·
            refine ⟨80599507328845347759070339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107466009771793797012093785 80599507328845347759070339)
            ·
              refine ⟨120899260993268021638605509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80599507328845347759070339 120899260993268021638605509)
              ·
                refine ⟨22668611436237754057238533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120899260993268021638605509 22668611436237754057238533)
                ·
                  refine ⟨4250364644294578885732225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22668611436237754057238533 4250364644294578885732225)
                  ·
                    refine ⟨3187773483220934164299169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250364644294578885732225 3187773483220934164299169)
                    ·
                      refine ⟨2390830112415700623224377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187773483220934164299169 2390830112415700623224377)
                      ·
                        rfl

theorem cell23_4656125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_4656125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656125 prefixEnd_4656125 := by exact prefixLift 4656125
  have htrace : WordTrace (prefixWord ++ tailWord_4656125) baseStart_4656125 baseEnd_4656125 := by
    simpa [prefixWord, tailWord_4656125, baseEnd_4656125] using wordTrace_append hprefix tailTrace_4656125
  have hstable : (prefixWord ++ tailWord_4656125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656125).length < 2 ^ (prefixWord ++ tailWord_4656125).sum := by decide
  have hdescent : baseEnd_4656125 < baseStart_4656125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656129 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_4656129 : Nat := 118140960795 + 4656129 * 2 ^ 59
def prefixEnd_4656129 : Nat := 4983230072969 + 3 ^ 40 * 4656129 * 2
def baseEnd_4656129 : Nat := 2390832166338318607574359

theorem tailTrace_4656129 : CollatzResearch.WordTrace tailWord_4656129 prefixEnd_4656129 2390832166338318607574359 := by
  unfold tailWord_4656129
  simp only [CollatzResearch.WordTrace]
  refine ⟨169822976148647311368923441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113215317432431540912615627 169822976148647311368923441)
  ·
    refine ⟨127367232111485483526692581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169822976148647311368923441 127367232111485483526692581)
    ·
      refine ⟨23881356020903528161254859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127367232111485483526692581 23881356020903528161254859)
      ·
        refine ⟨35822034031355292241882289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23881356020903528161254859 35822034031355292241882289)
        ·
          refine ⟨26866525523516469181411717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35822034031355292241882289 26866525523516469181411717)
          ·
            refine ⟨5037473535659337971514697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26866525523516469181411717 5037473535659337971514697)
            ·
              refine ⟨3778105151744503478636023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5037473535659337971514697 3778105151744503478636023)
              ·
                refine ⟨5667157727616755217954035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778105151744503478636023 5667157727616755217954035)
                ·
                  refine ⟨8500736591425132826931053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667157727616755217954035 8500736591425132826931053)
                  ·
                    refine ⟨3187776221784424810099145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8500736591425132826931053 3187776221784424810099145)
                    ·
                      refine ⟨2390832166338318607574359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187776221784424810099145 2390832166338318607574359)
                      ·
                        rfl

theorem cell23_4656129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_4656129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656129 prefixEnd_4656129 := by exact prefixLift 4656129
  have htrace : WordTrace (prefixWord ++ tailWord_4656129) baseStart_4656129 baseEnd_4656129 := by
    simpa [prefixWord, tailWord_4656129, baseEnd_4656129] using wordTrace_append hprefix tailTrace_4656129
  have hstable : (prefixWord ++ tailWord_4656129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656129).length < 2 ^ (prefixWord ++ tailWord_4656129).sum := by decide
  have hdescent : baseEnd_4656129 < baseStart_4656129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656138 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4656138 : Nat := 118140960795 + 4656138 * 2 ^ 59
def prefixEnd_4656138 : Nat := 4983230072969 + 3 ^ 40 * 4656138 * 2
def baseEnd_4656138 : Nat := 2390836787664209072361817

theorem tailTrace_4656138 : CollatzResearch.WordTrace tailWord_4656138 prefixEnd_4656138 2390836787664209072361817 := by
  unfold tailWord_4656138
  simp only [CollatzResearch.WordTrace]
  refine ⟨42455826101403676476500267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113215536270409803937334045 42455826101403676476500267)
  ·
    refine ⟨63683739152105514714750401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42455826101403676476500267 63683739152105514714750401)
    ·
      refine ⟨47762804364079136036062801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63683739152105514714750401 47762804364079136036062801)
      ·
        refine ⟨35822103273059352027047101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47762804364079136036062801 35822103273059352027047101)
        ·
          refine ⟨13433288727397257010142663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35822103273059352027047101 13433288727397257010142663)
          ·
            refine ⟨20149933091095885515213995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13433288727397257010142663 20149933091095885515213995)
            ·
              refine ⟨30224899636643828272820993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20149933091095885515213995 30224899636643828272820993)
              ·
                refine ⟨22668674727482871204615745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30224899636643828272820993 22668674727482871204615745)
                ·
                  refine ⟨17001506045612153403461809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22668674727482871204615745 17001506045612153403461809)
                  ·
                    refine ⟨12751129534209115052596357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17001506045612153403461809 12751129534209115052596357)
                    ·
                      refine ⟨2390836787664209072361817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12751129534209115052596357 2390836787664209072361817)
                      ·
                        rfl

theorem cell23_4656138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4656138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656138 prefixEnd_4656138 := by exact prefixLift 4656138
  have htrace : WordTrace (prefixWord ++ tailWord_4656138) baseStart_4656138 baseEnd_4656138 := by
    simpa [prefixWord, tailWord_4656138, baseEnd_4656138] using wordTrace_append hprefix tailTrace_4656138
  have hstable : (prefixWord ++ tailWord_4656138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656138).length < 2 ^ (prefixWord ++ tailWord_4656138).sum := by decide
  have hdescent : baseEnd_4656138 < baseStart_4656138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656142 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4656142 : Nat := 118140960795 + 4656142 * 2 ^ 59
def prefixEnd_4656142 : Nat := 4983230072969 + 3 ^ 40 * 4656142 * 2
def baseEnd_4656142 : Nat := 2390838841586827056711799

theorem tailTrace_4656142 : CollatzResearch.WordTrace tailWord_4656142 prefixEnd_4656142 2390838841586827056711799 := by
  unfold tailWord_4656142
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227931287200026823643335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113215633531733476392764453 21227931287200026823643335)
  ·
    refine ⟨31841896930800040235465003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21227931287200026823643335 31841896930800040235465003)
    ·
      refine ⟨47762845396200060353197505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31841896930800040235465003 47762845396200060353197505)
      ·
        refine ⟨35822134047150045264898129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47762845396200060353197505 35822134047150045264898129)
        ·
          refine ⟨26866600535362533948673597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35822134047150045264898129 26866600535362533948673597)
          ·
            refine ⟨10074975200760950230752599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26866600535362533948673597 10074975200760950230752599)
            ·
              refine ⟨15112462801141425346128899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10074975200760950230752599 15112462801141425346128899)
              ·
                refine ⟨22668694201712138019193349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15112462801141425346128899 22668694201712138019193349)
                ·
                  refine ⟨4250380162821025878598753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22668694201712138019193349 4250380162821025878598753)
                  ·
                    refine ⟨3187785122115769408949065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250380162821025878598753 3187785122115769408949065)
                    ·
                      refine ⟨2390838841586827056711799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187785122115769408949065 2390838841586827056711799)
                      ·
                        rfl

theorem cell23_4656142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4656142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656142 prefixEnd_4656142 := by exact prefixLift 4656142
  have htrace : WordTrace (prefixWord ++ tailWord_4656142) baseStart_4656142 baseEnd_4656142 := by
    simpa [prefixWord, tailWord_4656142, baseEnd_4656142] using wordTrace_append hprefix tailTrace_4656142
  have hstable : (prefixWord ++ tailWord_4656142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656142).length < 2 ^ (prefixWord ++ tailWord_4656142).sum := by decide
  have hdescent : baseEnd_4656142 < baseStart_4656142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656159 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 2, 2, 2]
def baseStart_4656159 : Nat := 118140960795 + 4656159 * 2 ^ 59
def prefixEnd_4656159 : Nat := 4983230072969 + 3 ^ 40 * 4656159 * 2
def baseEnd_4656159 : Nat := 2390847570757953490199221

theorem tailTrace_4656159 : CollatzResearch.WordTrace tailWord_4656159 prefixEnd_4656159 2390847570757953490199221 := by
  unfold tailWord_4656159
  simp only [CollatzResearch.WordTrace]
  refine ⟨169824070338538626492515531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113216046892359084328343687 169824070338538626492515531)
  ·
    refine ⟨254736105507807939738773297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169824070338538626492515531 254736105507807939738773297)
    ·
      refine ⟨191052079130855954804079973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254736105507807939738773297 191052079130855954804079973)
      ·
        refine ⟨35822264837035491525764995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191052079130855954804079973 35822264837035491525764995)
        ·
          refine ⟨53733397255553237288647493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35822264837035491525764995 53733397255553237288647493)
          ·
            refine ⟨10075011985416231991621405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53733397255553237288647493 10075011985416231991621405)
            ·
              refine ⟨3778129494531086996858027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10075011985416231991621405 3778129494531086996858027)
              ·
                refine ⟨5667194241796630495287041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778129494531086996858027 5667194241796630495287041)
                ·
                  refine ⟨4250395681347472871465281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5667194241796630495287041 4250395681347472871465281)
                  ·
                    refine ⟨3187796761010604653598961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250395681347472871465281 3187796761010604653598961)
                    ·
                      refine ⟨2390847570757953490199221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187796761010604653598961 2390847570757953490199221)
                      ·
                        rfl

theorem cell23_4656159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_4656159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656159 prefixEnd_4656159 := by exact prefixLift 4656159
  have htrace : WordTrace (prefixWord ++ tailWord_4656159) baseStart_4656159 baseEnd_4656159 := by
    simpa [prefixWord, tailWord_4656159, baseEnd_4656159] using wordTrace_append hprefix tailTrace_4656159
  have hstable : (prefixWord ++ tailWord_4656159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656159).length < 2 ^ (prefixWord ++ tailWord_4656159).sum := by decide
  have hdescent : baseEnd_4656159 < baseStart_4656159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656178 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_4656178 : Nat := 118140960795 + 4656178 * 2 ^ 59
def prefixEnd_4656178 : Nat := 4983230072969 + 3 ^ 40 * 4656178 * 2
def baseEnd_4656178 : Nat := 796952442296796305287211

theorem tailTrace_4656178 : CollatzResearch.WordTrace tailWord_4656178 prefixEnd_4656178 796952442296796305287211 := by
  unfold tailWord_4656178
  simp only [CollatzResearch.WordTrace]
  refine ⟨42456190831367448184364297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113216508883646528491638125 42456190831367448184364297)
  ·
    refine ⟨31842143123525586138273223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42456190831367448184364297 31842143123525586138273223)
    ·
      refine ⟨47763214685288379207409835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31842143123525586138273223 47763214685288379207409835)
      ·
        refine ⟨71644822027932568811114753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47763214685288379207409835 71644822027932568811114753)
        ·
          refine ⟨53733616520949426608336065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71644822027932568811114753 53733616520949426608336065)
          ·
            refine ⟨40300212390712069956252049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53733616520949426608336065 40300212390712069956252049)
            ·
              refine ⟨30225159293034052467189037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40300212390712069956252049 30225159293034052467189037)
              ·
                refine ⟨11334434734887769675195889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30225159293034052467189037 11334434734887769675195889)
                ·
                  refine ⟨8500826051165827256396917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11334434734887769675195889 8500826051165827256396917)
                  ·
                    refine ⟨796952442296796305287211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8500826051165827256396917 796952442296796305287211)
                    ·
                      rfl

theorem cell23_4656178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_4656178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656178 prefixEnd_4656178 := by exact prefixLift 4656178
  have htrace : WordTrace (prefixWord ++ tailWord_4656178) baseStart_4656178 baseEnd_4656178 := by
    simpa [prefixWord, tailWord_4656178, baseEnd_4656178] using wordTrace_append hprefix tailTrace_4656178
  have hstable : (prefixWord ++ tailWord_4656178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656178).length < 2 ^ (prefixWord ++ tailWord_4656178).sum := by decide
  have hdescent : baseEnd_4656178 < baseStart_4656178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656182 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_4656182 : Nat := 118140960795 + 4656182 * 2 ^ 59
def prefixEnd_4656182 : Nat := 4983230072969 + 3 ^ 40 * 4656182 * 2
def baseEnd_4656182 : Nat := 265651042312556322245735

theorem tailTrace_4656182 : CollatzResearch.WordTrace tailWord_4656182 prefixEnd_4656182 265651042312556322245735 := by
  unfold tailWord_4656182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614056826090956338787675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113216606144970200947068533 10614056826090956338787675)
  ·
    refine ⟨15921085239136434508181513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10614056826090956338787675 15921085239136434508181513)
    ·
      refine ⟨11940813929352325881136135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15921085239136434508181513 11940813929352325881136135)
      ·
        refine ⟨17911220894028488821704203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940813929352325881136135 17911220894028488821704203)
        ·
          refine ⟨26866831341042733232556305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17911220894028488821704203 26866831341042733232556305)
          ·
            refine ⟨20150123505782049924417229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26866831341042733232556305 20150123505782049924417229)
            ·
              refine ⟨7556296314668268721656461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20150123505782049924417229 7556296314668268721656461)
              ·
                refine ⟨2833611118000600770621173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7556296314668268721656461 2833611118000600770621173)
                ·
                  refine ⟨265651042312556322245735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2833611118000600770621173 265651042312556322245735)
                  ·
                    rfl

theorem cell23_4656182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_4656182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656182 prefixEnd_4656182 := by exact prefixLift 4656182
  have htrace : WordTrace (prefixWord ++ tailWord_4656182) baseStart_4656182 baseEnd_4656182 := by
    simpa [prefixWord, tailWord_4656182, baseEnd_4656182] using wordTrace_append hprefix tailTrace_4656182
  have hstable : (prefixWord ++ tailWord_4656182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656182).length < 2 ^ (prefixWord ++ tailWord_4656182).sum := by decide
  have hdescent : baseEnd_4656182 < baseStart_4656182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656201 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_4656201 : Nat := 118140960795 + 4656201 * 2 ^ 59
def prefixEnd_4656201 : Nat := 4983230072969 + 3 ^ 40 * 4656201 * 2
def baseEnd_4656201 : Nat := 2390869136945442325874027

theorem tailTrace_4656201 : CollatzResearch.WordTrace tailWord_4656201 prefixEnd_4656201 2390869136945442325874027 := by
  unfold tailWord_4656201
  simp only [CollatzResearch.WordTrace]
  refine ⟨169825602204386467665544457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113217068136257645110362971 169825602204386467665544457)
  ·
    refine ⟨127369201653289850749158343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169825602204386467665544457 127369201653289850749158343)
    ·
      refine ⟨191053802479934776123737515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127369201653289850749158343 191053802479934776123737515)
      ·
        refine ⟨286580703719902164185606273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191053802479934776123737515 286580703719902164185606273)
        ·
          refine ⟨214935527789926623139204705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286580703719902164185606273 214935527789926623139204705)
          ·
            refine ⟨161201645842444967354403529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214935527789926623139204705 161201645842444967354403529)
            ·
              refine ⟨120901234381833725515802647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161201645842444967354403529 120901234381833725515802647)
              ·
                refine ⟨181351851572750588273703971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120901234381833725515802647 181351851572750588273703971)
                ·
                  refine ⟨272027777359125882410555957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181351851572750588273703971 272027777359125882410555957)
                  ·
                    refine ⟨25502604127418051475989621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 272027777359125882410555957 25502604127418051475989621)
                    ·
                      refine ⟨2390869136945442325874027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25502604127418051475989621 2390869136945442325874027)
                      ·
                        rfl

theorem cell23_4656201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_4656201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656201 prefixEnd_4656201 := by exact prefixLift 4656201
  have htrace : WordTrace (prefixWord ++ tailWord_4656201) baseStart_4656201 baseEnd_4656201 := by
    simpa [prefixWord, tailWord_4656201, baseEnd_4656201] using wordTrace_append hprefix tailTrace_4656201
  have hstable : (prefixWord ++ tailWord_4656201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656201).length < 2 ^ (prefixWord ++ tailWord_4656201).sum := by decide
  have hdescent : baseEnd_4656201 < baseStart_4656201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656205 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_4656205 : Nat := 118140960795 + 4656205 * 2 ^ 59
def prefixEnd_4656205 : Nat := 4983230072969 + 3 ^ 40 * 4656205 * 2
def baseEnd_4656205 : Nat := 2390871190868060310224009

theorem tailTrace_4656205 : CollatzResearch.WordTrace tailWord_4656205 prefixEnd_4656205 2390871190868060310224009 := by
  unfold tailWord_4656205
  simp only [CollatzResearch.WordTrace]
  refine ⟨169825748096371976348690069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113217165397581317565793379 169825748096371976348690069)
  ·
    refine ⟨7960581942017436391344847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169825748096371976348690069 7960581942017436391344847)
    ·
      refine ⟨11940872913026154587017271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7960581942017436391344847 11940872913026154587017271)
      ·
        refine ⟨17911309369539231880525907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940872913026154587017271 17911309369539231880525907)
        ·
          refine ⟨26866964054308847820788861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17911309369539231880525907 26866964054308847820788861)
          ·
            refine ⟨10075111520365817932795823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26866964054308847820788861 10075111520365817932795823)
            ·
              refine ⟨15112667280548726899193735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10075111520365817932795823 15112667280548726899193735)
              ·
                refine ⟨22669000920823090348790603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15112667280548726899193735 22669000920823090348790603)
                ·
                  refine ⟨34003501381234635523185905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22669000920823090348790603 34003501381234635523185905)
                  ·
                    refine ⟨25502626035925976642389429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34003501381234635523185905 25502626035925976642389429)
                    ·
                      refine ⟨2390871190868060310224009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25502626035925976642389429 2390871190868060310224009)
                      ·
                        rfl

theorem cell23_4656205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_4656205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656205 prefixEnd_4656205 := by exact prefixLift 4656205
  have htrace : WordTrace (prefixWord ++ tailWord_4656205) baseStart_4656205 baseEnd_4656205 := by
    simpa [prefixWord, tailWord_4656205, baseEnd_4656205] using wordTrace_append hprefix tailTrace_4656205
  have hstable : (prefixWord ++ tailWord_4656205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656205).length < 2 ^ (prefixWord ++ tailWord_4656205).sum := by decide
  have hdescent : baseEnd_4656205 < baseStart_4656205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656211 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_4656211 : Nat := 118140960795 + 4656211 * 2 ^ 59
def prefixEnd_4656211 : Nat := 4983230072969 + 3 ^ 40 * 4656211 * 2
def baseEnd_4656211 : Nat := 2390874271751987286748981

theorem tailTrace_4656211 : CollatzResearch.WordTrace tailWord_4656211 prefixEnd_4656211 2390874271751987286748981 := by
  unfold tailWord_4656211
  simp only [CollatzResearch.WordTrace]
  refine ⟨169825966934350239373408487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113217311289566826248938991 169825966934350239373408487)
  ·
    refine ⟨254738950401525359060112731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169825966934350239373408487 254738950401525359060112731)
    ·
      refine ⟨382108425602288038590169097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254738950401525359060112731 382108425602288038590169097)
      ·
        refine ⟨286581319201716028942626823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382108425602288038590169097 286581319201716028942626823)
        ·
          refine ⟨429871978802574043413940235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286581319201716028942626823 429871978802574043413940235)
          ·
            refine ⟨644807968203861065120910353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429871978802574043413940235 644807968203861065120910353)
            ·
              refine ⟨483605976152895798840682765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644807968203861065120910353 483605976152895798840682765)
              ·
                refine ⟨181352241057335924565256037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483605976152895798840682765 181352241057335924565256037)
                ·
                  refine ⟨34003545198250485855985507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181352241057335924565256037 34003545198250485855985507)
                  ·
                    refine ⟨51005317797375728783978261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34003545198250485855985507 51005317797375728783978261)
                    ·
                      refine ⟨2390874271751987286748981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51005317797375728783978261 2390874271751987286748981)
                      ·
                        rfl

theorem cell23_4656211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_4656211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656211 prefixEnd_4656211 := by exact prefixLift 4656211
  have htrace : WordTrace (prefixWord ++ tailWord_4656211) baseStart_4656211 baseEnd_4656211 := by
    simpa [prefixWord, tailWord_4656211, baseEnd_4656211] using wordTrace_append hprefix tailTrace_4656211
  have hstable : (prefixWord ++ tailWord_4656211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656211).length < 2 ^ (prefixWord ++ tailWord_4656211).sum := by decide
  have hdescent : baseEnd_4656211 < baseStart_4656211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656218 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_4656218 : Nat := 118140960795 + 4656218 * 2 ^ 59
def prefixEnd_4656218 : Nat := 4983230072969 + 3 ^ 40 * 4656218 * 2
def baseEnd_4656218 : Nat := 2390877866116568759361449

theorem tailTrace_4656218 : CollatzResearch.WordTrace tailWord_4656218 prefixEnd_4656218 2390877866116568759361449 := by
  unfold tailWord_4656218
  simp only [CollatzResearch.WordTrace]
  refine ⟨42456555561331219892228327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113217481496883253045942205 42456555561331219892228327)
  ·
    refine ⟨63684833341996829838342491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42456555561331219892228327 63684833341996829838342491)
    ·
      refine ⟨95527250012995244757513737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63684833341996829838342491 95527250012995244757513737)
      ·
        refine ⟨71645437509746433568135303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95527250012995244757513737 71645437509746433568135303)
        ·
          refine ⟨107468156264619650352202955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71645437509746433568135303 107468156264619650352202955)
          ·
            refine ⟨161202234396929475528304433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107468156264619650352202955 161202234396929475528304433)
            ·
              refine ⟨120901675797697106646228325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161202234396929475528304433 120901675797697106646228325)
              ·
                refine ⟨22669064212068207496167811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120901675797697106646228325 22669064212068207496167811)
                ·
                  refine ⟨34003596318102311244251717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22669064212068207496167811 34003596318102311244251717)
                  ·
                    refine ⟨6375674309644183358297197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34003596318102311244251717 6375674309644183358297197)
                    ·
                      refine ⟨2390877866116568759361449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6375674309644183358297197 2390877866116568759361449)
                      ·
                        rfl

theorem cell23_4656218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_4656218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656218 prefixEnd_4656218 := by exact prefixLift 4656218
  have htrace : WordTrace (prefixWord ++ tailWord_4656218) baseStart_4656218 baseEnd_4656218 := by
    simpa [prefixWord, tailWord_4656218, baseEnd_4656218] using wordTrace_append hprefix tailTrace_4656218
  have hstable : (prefixWord ++ tailWord_4656218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656218).length < 2 ^ (prefixWord ++ tailWord_4656218).sum := by decide
  have hdescent : baseEnd_4656218 < baseStart_4656218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656242 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_4656242 : Nat := 118140960795 + 4656242 * 2 ^ 59
def prefixEnd_4656242 : Nat := 4983230072969 + 3 ^ 40 * 4656242 * 2
def baseEnd_4656242 : Nat := 796963396550758888487113

theorem tailTrace_4656242 : CollatzResearch.WordTrace tailWord_4656242 prefixEnd_4656242 796963396550758888487113 := by
  unfold tailWord_4656242
  simp only [CollatzResearch.WordTrace]
  refine ⟨42456774399309482916946745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113218065064825287778524653 42456774399309482916946745)
  ·
    refine ⟨31842580799482112187710059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42456774399309482916946745 31842580799482112187710059)
    ·
      refine ⟨47763871199223168281565089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31842580799482112187710059 47763871199223168281565089)
      ·
        refine ⟨35822903399417376211173817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47763871199223168281565089 35822903399417376211173817)
        ·
          refine ⟨26867177549563032158380363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35822903399417376211173817 26867177549563032158380363)
          ·
            refine ⟨40300766324344548237570545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26867177549563032158380363 40300766324344548237570545)
            ·
              refine ⟨30225574743258411178177909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40300766324344548237570545 30225574743258411178177909)
              ·
                refine ⟨2833647632180476047954179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30225574743258411178177909 2833647632180476047954179)
                ·
                  refine ⟨4250471448270714071931269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833647632180476047954179 4250471448270714071931269)
                  ·
                    refine ⟨796963396550758888487113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250471448270714071931269 796963396550758888487113)
                    ·
                      rfl

theorem cell23_4656242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_4656242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656242 prefixEnd_4656242 := by exact prefixLift 4656242
  have htrace : WordTrace (prefixWord ++ tailWord_4656242) baseStart_4656242 baseEnd_4656242 := by
    simpa [prefixWord, tailWord_4656242, baseEnd_4656242] using wordTrace_append hprefix tailTrace_4656242
  have hstable : (prefixWord ++ tailWord_4656242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656242).length < 2 ^ (prefixWord ++ tailWord_4656242).sum := by decide
  have hdescent : baseEnd_4656242 < baseStart_4656242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656275 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 4, 3, 2]
def baseStart_4656275 : Nat := 118140960795 + 4656275 * 2 ^ 59
def prefixEnd_4656275 : Nat := 4983230072969 + 3 ^ 40 * 4656275 * 2
def baseEnd_4656275 : Nat := 2390907134513875036348687

theorem tailTrace_4656275 : CollatzResearch.WordTrace tailWord_4656275 prefixEnd_4656275 2390907134513875036348687 := by
  unfold tailWord_4656275
  simp only [CollatzResearch.WordTrace]
  refine ⟨169828301206118378303738279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113218867470745585535825519 169828301206118378303738279)
  ·
    refine ⟨254742451809177567455607419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169828301206118378303738279 254742451809177567455607419)
    ·
      refine ⟨382113677713766351183411129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254742451809177567455607419 382113677713766351183411129)
      ·
        refine ⟨286585258285324763387558347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382113677713766351183411129 286585258285324763387558347)
        ·
          refine ⟨429877887427987145081337521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286585258285324763387558347 429877887427987145081337521)
          ·
            refine ⟨322408415570990358811003141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429877887427987145081337521 322408415570990358811003141)
            ·
              refine ⟨60451577919560692277063089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 322408415570990358811003141 60451577919560692277063089)
              ·
                refine ⟨45338683439670519207797317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60451577919560692277063089 45338683439670519207797317)
                ·
                  refine ⟨8501003144938222351461997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45338683439670519207797317 8501003144938222351461997)
                  ·
                    refine ⟨3187876179351833381798249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8501003144938222351461997 3187876179351833381798249)
                    ·
                      refine ⟨2390907134513875036348687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187876179351833381798249 2390907134513875036348687)
                      ·
                        rfl

theorem cell23_4656275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3, 2].length) (baseStart_4656275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656275 prefixEnd_4656275 := by exact prefixLift 4656275
  have htrace : WordTrace (prefixWord ++ tailWord_4656275) baseStart_4656275 baseEnd_4656275 := by
    simpa [prefixWord, tailWord_4656275, baseEnd_4656275] using wordTrace_append hprefix tailTrace_4656275
  have hstable : (prefixWord ++ tailWord_4656275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656275).length < 2 ^ (prefixWord ++ tailWord_4656275).sum := by decide
  have hdescent : baseEnd_4656275 < baseStart_4656275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656282 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4656282 : Nat := 118140960795 + 4656282 * 2 ^ 59
def prefixEnd_4656282 : Nat := 4983230072969 + 3 ^ 40 * 4656282 * 2
def baseEnd_4656282 : Nat := 2390910728878456508961155

theorem tailTrace_4656282 : CollatzResearch.WordTrace tailWord_4656282 prefixEnd_4656282 2390910728878456508961155 := by
  unfold tailWord_4656282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42457139129273254624810775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113219037678062012332828733 42457139129273254624810775)
  ·
    refine ⟨63685708693909881937216163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42457139129273254624810775 63685708693909881937216163)
    ·
      refine ⟨95528563040864822905824245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63685708693909881937216163 95528563040864822905824245)
      ·
        refine ⟨8955802785081077147421023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95528563040864822905824245 8955802785081077147421023)
        ·
          refine ⟨13433704177621615721131535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8955802785081077147421023 13433704177621615721131535)
          ·
            refine ⟨20150556266432423581697303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13433704177621615721131535 20150556266432423581697303)
            ·
              refine ⟨30225834399648635372545955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20150556266432423581697303 30225834399648635372545955)
              ·
                refine ⟨45338751599472953058818933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30225834399648635372545955 45338751599472953058818933)
                ·
                  refine ⟨4250507962450589349264275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45338751599472953058818933 4250507962450589349264275)
                  ·
                    refine ⟨6375761943675884023896413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4250507962450589349264275 6375761943675884023896413)
                    ·
                      refine ⟨2390910728878456508961155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6375761943675884023896413 2390910728878456508961155)
                      ·
                        rfl

theorem cell23_4656282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4656282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656282 prefixEnd_4656282 := by exact prefixLift 4656282
  have htrace : WordTrace (prefixWord ++ tailWord_4656282) baseStart_4656282 baseEnd_4656282 := by
    simpa [prefixWord, tailWord_4656282, baseEnd_4656282] using wordTrace_append hprefix tailTrace_4656282
  have hstable : (prefixWord ++ tailWord_4656282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656282).length < 2 ^ (prefixWord ++ tailWord_4656282).sum := by decide
  have hdescent : baseEnd_4656282 < baseStart_4656282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656285 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_4656285 : Nat := 118140960795 + 4656285 * 2 ^ 59
def prefixEnd_4656285 : Nat := 4983230072969 + 3 ^ 40 * 4656285 * 2
def baseEnd_4656285 : Nat := 796970756440139999074547

theorem tailTrace_4656285 : CollatzResearch.WordTrace tailWord_4656285 prefixEnd_4656285 796970756440139999074547 := by
  unfold tailWord_4656285
  simp only [CollatzResearch.WordTrace]
  refine ⟨169828665936082150011602309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113219110624054766674401539 169828665936082150011602309)
  ·
    refine ⟨31842874863015403127175433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169828665936082150011602309 31842874863015403127175433)
    ·
      refine ⟨23882156147261552345381575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31842874863015403127175433 23882156147261552345381575)
      ·
        refine ⟨35823234220892328518072363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23882156147261552345381575 35823234220892328518072363)
        ·
          refine ⟨53734851331338492777108545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35823234220892328518072363 53734851331338492777108545)
          ·
            refine ⟨40301138498503869582831409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53734851331338492777108545 40301138498503869582831409)
            ·
              refine ⟨30225853873877902187123557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40301138498503869582831409 30225853873877902187123557)
              ·
                refine ⟨5667347601352106660085667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30225853873877902187123557 5667347601352106660085667)
                ·
                  refine ⟨8501021402028159990128501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667347601352106660085667 8501021402028159990128501)
                  ·
                    refine ⟨796970756440139999074547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8501021402028159990128501 796970756440139999074547)
                    ·
                      rfl

theorem cell23_4656285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_4656285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656285 prefixEnd_4656285 := by exact prefixLift 4656285
  have htrace : WordTrace (prefixWord ++ tailWord_4656285) baseStart_4656285 baseEnd_4656285 := by
    simpa [prefixWord, tailWord_4656285, baseEnd_4656285] using wordTrace_append hprefix tailTrace_4656285
  have hstable : (prefixWord ++ tailWord_4656285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656285).length < 2 ^ (prefixWord ++ tailWord_4656285).sum := by decide
  have hdescent : baseEnd_4656285 < baseStart_4656285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656292 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_4656292 : Nat := 118140960795 + 4656292 * 2 ^ 59
def prefixEnd_4656292 : Nat := 4983230072969 + 3 ^ 40 * 4656292 * 2
def baseEnd_4656292 : Nat := 2390915863685001469836109

theorem tailTrace_4656292 : CollatzResearch.WordTrace tailWord_4656292 prefixEnd_4656292 2390915863685001469836109 := by
  unfold tailWord_4656292
  simp only [CollatzResearch.WordTrace]
  refine ⟨84914460623528395103553565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113219280831371193471404753 84914460623528395103553565)
  ·
    refine ⟨31842922733823148163832587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84914460623528395103553565 31842922733823148163832587)
    ·
      refine ⟨47764384100734722245748881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31842922733823148163832587 47764384100734722245748881)
      ·
        refine ⟨35823288075551041684311661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47764384100734722245748881 35823288075551041684311661)
        ·
          refine ⟨13433733028331640631616873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35823288075551041684311661 13433733028331640631616873)
          ·
            refine ⟨10075299771248730473712655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13433733028331640631616873 10075299771248730473712655)
            ·
              refine ⟨15112949656873095710568983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10075299771248730473712655 15112949656873095710568983)
              ·
                refine ⟨22669424485309643565853475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15112949656873095710568983 22669424485309643565853475)
                ·
                  refine ⟨34004136727964465348780213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22669424485309643565853475 34004136727964465348780213)
                  ·
                    refine ⟨3187887818246668626448145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34004136727964465348780213 3187887818246668626448145)
                    ·
                      refine ⟨2390915863685001469836109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187887818246668626448145 2390915863685001469836109)
                      ·
                        rfl

theorem cell23_4656292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_4656292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656292 prefixEnd_4656292 := by exact prefixLift 4656292
  have htrace : WordTrace (prefixWord ++ tailWord_4656292) baseStart_4656292 baseEnd_4656292 := by
    simpa [prefixWord, tailWord_4656292, baseEnd_4656292] using wordTrace_append hprefix tailTrace_4656292
  have hstable : (prefixWord ++ tailWord_4656292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656292).length < 2 ^ (prefixWord ++ tailWord_4656292).sum := by decide
  have hdescent : baseEnd_4656292 < baseStart_4656292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656315 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 2, 4]
def baseStart_4656315 : Nat := 118140960795 + 4656315 * 2 ^ 59
def prefixEnd_4656315 : Nat := 4983230072969 + 3 ^ 40 * 4656315 * 2
def baseEnd_4656315 : Nat := 796975891246684959949501

theorem tailTrace_4656315 : CollatzResearch.WordTrace tailWord_4656315 prefixEnd_4656315 796975891246684959949501 := by
  unfold tailWord_4656315
  simp only [CollatzResearch.WordTrace]
  refine ⟨169829760125973465135194399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113219840083982310090129599 169829760125973465135194399)
  ·
    refine ⟨254744640188960197702791599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169829760125973465135194399 254744640188960197702791599)
    ·
      refine ⟨382116960283440296554187399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254744640188960197702791599 382116960283440296554187399)
      ·
        refine ⟨573175440425160444831281099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382116960283440296554187399 573175440425160444831281099)
        ·
          refine ⟨859763160637740667246921649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573175440425160444831281099 859763160637740667246921649)
          ·
            refine ⟨644822370478305500435191237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859763160637740667246921649 644822370478305500435191237)
            ·
              refine ⟨120904194464682281331598357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 644822370478305500435191237 120904194464682281331598357)
              ·
                refine ⟨5667384115531981937418673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120904194464682281331598357 5667384115531981937418673)
                ·
                  refine ⟨4250538086648986453064005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5667384115531981937418673 4250538086648986453064005)
                  ·
                    refine ⟨796975891246684959949501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250538086648986453064005 796975891246684959949501)
                    ·
                      rfl

theorem cell23_4656315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 4].length) (baseStart_4656315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656315 prefixEnd_4656315 := by exact prefixLift 4656315
  have htrace : WordTrace (prefixWord ++ tailWord_4656315) baseStart_4656315 baseEnd_4656315 := by
    simpa [prefixWord, tailWord_4656315, baseEnd_4656315] using wordTrace_append hprefix tailTrace_4656315
  have hstable : (prefixWord ++ tailWord_4656315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656315).length < 2 ^ (prefixWord ++ tailWord_4656315).sum := by decide
  have hdescent : baseEnd_4656315 < baseStart_4656315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656356 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_4656356 : Nat := 118140960795 + 4656356 * 2 ^ 59
def prefixEnd_4656356 : Nat := 4983230072969 + 3 ^ 40 * 4656356 * 2
def baseEnd_4656356 : Nat := 2390948726446889219435815

theorem tailTrace_4656356 : CollatzResearch.WordTrace tailWord_4656356 prefixEnd_4656356 2390948726446889219435815 := by
  unfold tailWord_4656356
  simp only [CollatzResearch.WordTrace]
  refine ⟨84915627759412464568718461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113220837012549952758291281 84915627759412464568718461)
  ·
    refine ⟨31843360409779674213269423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84915627759412464568718461 31843360409779674213269423)
    ·
      refine ⟨47765040614669511319904135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31843360409779674213269423 47765040614669511319904135)
      ·
        refine ⟨71647560922004266979856203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47765040614669511319904135 71647560922004266979856203)
        ·
          refine ⟨107471341383006400469784305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71647560922004266979856203 107471341383006400469784305)
          ·
            refine ⟨80603506037254800352338229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107471341383006400469784305 80603506037254800352338229)
            ·
              refine ⟨7556578690992637533031709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80603506037254800352338229 7556578690992637533031709)
              ·
                refine ⟨2833717009122239074886891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7556578690992637533031709 2833717009122239074886891)
                ·
                  refine ⟨4250575513683358612330337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833717009122239074886891 4250575513683358612330337)
                  ·
                    refine ⟨3187931635262518959247753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250575513683358612330337 3187931635262518959247753)
                    ·
                      refine ⟨2390948726446889219435815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187931635262518959247753 2390948726446889219435815)
                      ·
                        rfl

theorem cell23_4656356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_4656356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656356 prefixEnd_4656356 := by exact prefixLift 4656356
  have htrace : WordTrace (prefixWord ++ tailWord_4656356) baseStart_4656356 baseEnd_4656356 := by
    simpa [prefixWord, tailWord_4656356, baseEnd_4656356] using wordTrace_append hprefix tailTrace_4656356
  have hstable : (prefixWord ++ tailWord_4656356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656356).length < 2 ^ (prefixWord ++ tailWord_4656356).sum := by decide
  have hdescent : baseEnd_4656356 < baseStart_4656356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656412 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_4656412 : Nat := 118140960795 + 4656412 * 2 ^ 59
def prefixEnd_4656412 : Nat := 4983230072969 + 3 ^ 40 * 4656412 * 2
def baseEnd_4656412 : Nat := 2390977481363541000335557

theorem tailTrace_4656412 : CollatzResearch.WordTrace tailWord_4656412 prefixEnd_4656412 2390977481363541000335557 := by
  unfold tailWord_4656412
  simp only [CollatzResearch.WordTrace]
  refine ⟨84916649003311025350737745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113222198671081367134316993 84916649003311025350737745)
  ·
    refine ⟨63687486752483269013053309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84916649003311025350737745 63687486752483269013053309)
    ·
      refine ⟨23882807532181225879894991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63687486752483269013053309 23882807532181225879894991)
      ·
        refine ⟨35824211298271838819842487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23882807532181225879894991 35824211298271838819842487)
        ·
          refine ⟨53736316947407758229763731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35824211298271838819842487 53736316947407758229763731)
          ·
            refine ⟨80604475421111637344645597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53736316947407758229763731 80604475421111637344645597)
            ·
              refine ⟨30226678282916864004242099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80604475421111637344645597 30226678282916864004242099)
              ·
                refine ⟨45340017424375296006363149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30226678282916864004242099 45340017424375296006363149)
                ·
                  refine ⟨17002506534140736002386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45340017424375296006363149 17002506534140736002386181)
                  ·
                    refine ⟨3187969975151388000447409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17002506534140736002386181 3187969975151388000447409)
                    ·
                      refine ⟨2390977481363541000335557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187969975151388000447409 2390977481363541000335557)
                      ·
                        rfl

theorem cell23_4656412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_4656412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656412 prefixEnd_4656412 := by exact prefixLift 4656412
  have htrace : WordTrace (prefixWord ++ tailWord_4656412) baseStart_4656412 baseEnd_4656412 := by
    simpa [prefixWord, tailWord_4656412, baseEnd_4656412] using wordTrace_append hprefix tailTrace_4656412
  have hstable : (prefixWord ++ tailWord_4656412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656412).length < 2 ^ (prefixWord ++ tailWord_4656412).sum := by decide
  have hdescent : baseEnd_4656412 < baseStart_4656412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656446 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_4656446 : Nat := 118140960795 + 4656446 * 2 ^ 59
def prefixEnd_4656446 : Nat := 4983230072969 + 3 ^ 40 * 4656446 * 2
def baseEnd_4656446 : Nat := 2390994939705793867310401

theorem tailTrace_4656446 : CollatzResearch.WordTrace tailWord_4656446 prefixEnd_4656446 2390994939705793867310401 := by
  unfold tailWord_4656446
  simp only [CollatzResearch.WordTrace]
  refine ⟨21229317261062359313526649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113223025392332583005475461 21229317261062359313526649)
  ·
    refine ⟨15921987945796769485144987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21229317261062359313526649 15921987945796769485144987)
    ·
      refine ⟨23882981918695154227717481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15921987945796769485144987 23882981918695154227717481)
      ·
        refine ⟨17912236439021365670788111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23882981918695154227717481 17912236439021365670788111)
        ·
          refine ⟨26868354658532048506182167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17912236439021365670788111 26868354658532048506182167)
          ·
            refine ⟨40302531987798072759273251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26868354658532048506182167 40302531987798072759273251)
            ·
              refine ⟨60453797981697109138909877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40302531987798072759273251 60453797981697109138909877)
              ·
                refine ⟨5667543560784103981772801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60453797981697109138909877 5667543560784103981772801)
                ·
                  refine ⟨4250657670588077986329601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5667543560784103981772801 4250657670588077986329601)
                  ·
                    refine ⟨3187993252941058489747201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250657670588077986329601 3187993252941058489747201)
                    ·
                      refine ⟨2390994939705793867310401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3187993252941058489747201 2390994939705793867310401)
                      ·
                        rfl

theorem cell23_4656446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_4656446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656446 prefixEnd_4656446 := by exact prefixLift 4656446
  have htrace : WordTrace (prefixWord ++ tailWord_4656446) baseStart_4656446 baseEnd_4656446 := by
    simpa [prefixWord, tailWord_4656446, baseEnd_4656446] using wordTrace_append hprefix tailTrace_4656446
  have hstable : (prefixWord ++ tailWord_4656446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656446).length < 2 ^ (prefixWord ++ tailWord_4656446).sum := by decide
  have hdescent : baseEnd_4656446 < baseStart_4656446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656452 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 9]
def baseStart_4656452 : Nat := 118140960795 + 4656452 * 2 ^ 59
def prefixEnd_4656452 : Nat := 4983230072969 + 3 ^ 40 * 4656452 * 2
def baseEnd_4656452 : Nat := 265666446732191204870597

theorem tailTrace_4656452 : CollatzResearch.WordTrace tailWord_4656452 prefixEnd_4656452 265666446732191204870597 := by
  unfold tailWord_4656452
  simp only [CollatzResearch.WordTrace]
  refine ⟨84917378463238568766465805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113223171284318091688621073 84917378463238568766465805)
  ·
    refine ⟨31844016923714463287424677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84917378463238568766465805 31844016923714463287424677)
    ·
      refine ⟨5970753173196461866392127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31844016923714463287424677 5970753173196461866392127)
      ·
        refine ⟨8956129759794692799588191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970753173196461866392127 8956129759794692799588191)
        ·
          refine ⟨13434194639692039199382287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8956129759794692799588191 13434194639692039199382287)
          ·
            refine ⟨20151291959538058799073431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13434194639692039199382287 20151291959538058799073431)
            ·
              refine ⟨30226937939307088198610147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20151291959538058799073431 30226937939307088198610147)
              ·
                refine ⟨45340406908960632297915221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30226937939307088198610147 45340406908960632297915221)
                ·
                  refine ⟨265666446732191204870597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45340406908960632297915221 265666446732191204870597)
                  ·
                    rfl

theorem cell23_4656452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_4656452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656452 prefixEnd_4656452 := by exact prefixLift 4656452
  have htrace : WordTrace (prefixWord ++ tailWord_4656452) baseStart_4656452 baseEnd_4656452 := by
    simpa [prefixWord, tailWord_4656452, baseEnd_4656452] using wordTrace_append hprefix tailTrace_4656452
  have hstable : (prefixWord ++ tailWord_4656452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656452).length < 2 ^ (prefixWord ++ tailWord_4656452).sum := by decide
  have hdescent : baseEnd_4656452 < baseStart_4656452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656465 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_4656465 : Nat := 118140960795 + 4656465 * 2 ^ 59
def prefixEnd_4656465 : Nat := 4983230072969 + 3 ^ 40 * 4656465 * 2
def baseEnd_4656465 : Nat := 797001565279409764324271

theorem tailTrace_4656465 : CollatzResearch.WordTrace tailWord_4656465 prefixEnd_4656465 797001565279409764324271 := by
  unfold tailWord_4656465
  simp only [CollatzResearch.WordTrace]
  refine ⟨169835231075430040753154849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113223487383620027168769899 169835231075430040753154849)
  ·
    refine ⟨127376423306572530564866137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169835231075430040753154849 127376423306572530564866137)
    ·
      refine ⟨95532317479929397923649603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127376423306572530564866137 95532317479929397923649603)
      ·
        refine ⟨143298476219894096885474405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95532317479929397923649603 143298476219894096885474405)
        ·
          refine ⟨26868464291230143166026451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143298476219894096885474405 26868464291230143166026451)
          ·
            refine ⟨40302696436845214749039677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26868464291230143166026451 40302696436845214749039677)
            ·
              refine ⟨15113511163816955530889879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40302696436845214749039677 15113511163816955530889879)
              ·
                refine ⟨22670266745725433296334819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15113511163816955530889879 22670266745725433296334819)
                ·
                  refine ⟨34005400118588149944502229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22670266745725433296334819 34005400118588149944502229)
                  ·
                    refine ⟨797001565279409764324271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34005400118588149944502229 797001565279409764324271)
                    ·
                      rfl

theorem cell23_4656465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_4656465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656465 prefixEnd_4656465 := by exact prefixLift 4656465
  have htrace : WordTrace (prefixWord ++ tailWord_4656465) baseStart_4656465 baseEnd_4656465 := by
    simpa [prefixWord, tailWord_4656465, baseEnd_4656465] using wordTrace_append hprefix tailTrace_4656465
  have hstable : (prefixWord ++ tailWord_4656465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656465).length < 2 ^ (prefixWord ++ tailWord_4656465).sum := by decide
  have hdescent : baseEnd_4656465 < baseStart_4656465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656469 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 5]
def baseStart_4656469 : Nat := 118140960795 + 4656469 * 2 ^ 59
def prefixEnd_4656469 : Nat := 4983230072969 + 3 ^ 40 * 4656469 * 2
def baseEnd_4656469 : Nat := 265667416640094141924755

theorem tailTrace_4656469 : CollatzResearch.WordTrace tailWord_4656469 prefixEnd_4656469 265667416640094141924755 := by
  unfold tailWord_4656469
  simp only [CollatzResearch.WordTrace]
  refine ⟨169835376967415549436300461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113223584644943699624200307 169835376967415549436300461)
  ·
    refine ⟨63688266362780831038612673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169835376967415549436300461 63688266362780831038612673)
    ·
      refine ⟨47766199772085623278959505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63688266362780831038612673 47766199772085623278959505)
      ·
        refine ⟨35824649829064217459219629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47766199772085623278959505 35824649829064217459219629)
        ·
          refine ⟨13434243685899081547207361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35824649829064217459219629 13434243685899081547207361)
          ·
            refine ⟨10075682764424311160405521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13434243685899081547207361 10075682764424311160405521)
            ·
              refine ⟨7556762073318233370304141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10075682764424311160405521 7556762073318233370304141)
              ·
                refine ⟨2833785777494337513864053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7556762073318233370304141 2833785777494337513864053)
                ·
                  refine ⟨265667416640094141924755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2833785777494337513864053 265667416640094141924755)
                  ·
                    rfl

theorem cell23_4656469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_4656469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656469 prefixEnd_4656469 := by exact prefixLift 4656469
  have htrace : WordTrace (prefixWord ++ tailWord_4656469) baseStart_4656469 baseEnd_4656469 := by
    simpa [prefixWord, tailWord_4656469, baseEnd_4656469] using wordTrace_append hprefix tailTrace_4656469
  have hstable : (prefixWord ++ tailWord_4656469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656469).length < 2 ^ (prefixWord ++ tailWord_4656469).sum := by decide
  have hdescent : baseEnd_4656469 < baseStart_4656469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656482 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4656482 : Nat := 118140960795 + 4656482 * 2 ^ 59
def prefixEnd_4656482 : Nat := 4983230072969 + 3 ^ 40 * 4656482 * 2
def baseEnd_4656482 : Nat := 797004475003118575486745

theorem tailTrace_4656482 : CollatzResearch.WordTrace tailWord_4656482 prefixEnd_4656482 797004475003118575486745 := by
  unfold tailWord_4656482
  simp only [CollatzResearch.WordTrace]
  refine ⟨42458962779092113164130925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113223900744245635104349133 42458962779092113164130925)
  ·
    refine ⟨15922111042159542436549097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42458962779092113164130925 15922111042159542436549097)
    ·
      refine ⟨11941583281619656827411823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15922111042159542436549097 11941583281619656827411823)
      ·
        refine ⟨17912374922429485241117735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11941583281619656827411823 17912374922429485241117735)
        ·
          refine ⟨26868562383644227861676603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17912374922429485241117735 26868562383644227861676603)
          ·
            refine ⟨40302843575466341792514905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26868562383644227861676603 40302843575466341792514905)
            ·
              refine ⟨30227132681599756344386179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40302843575466341792514905 30227132681599756344386179)
              ·
                refine ⟨45340699022399634516579269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30227132681599756344386179 45340699022399634516579269)
                ·
                  refine ⟨8501381066699931471858613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45340699022399634516579269 8501381066699931471858613)
                  ·
                    refine ⟨797004475003118575486745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8501381066699931471858613 797004475003118575486745)
                    ·
                      rfl

theorem cell23_4656482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4656482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656482 prefixEnd_4656482 := by exact prefixLift 4656482
  have htrace : WordTrace (prefixWord ++ tailWord_4656482) baseStart_4656482 baseEnd_4656482 := by
    simpa [prefixWord, tailWord_4656482, baseEnd_4656482] using wordTrace_append hprefix tailTrace_4656482
  have hstable : (prefixWord ++ tailWord_4656482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656482).length < 2 ^ (prefixWord ++ tailWord_4656482).sum := by decide
  have hdescent : baseEnd_4656482 < baseStart_4656482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656546 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_4656546 : Nat := 118140960795 + 4656546 * 2 ^ 59
def prefixEnd_4656546 : Nat := 4983230072969 + 3 ^ 40 * 4656546 * 2
def baseEnd_4656546 : Nat := 797015429257081158686647

theorem tailTrace_4656546 : CollatzResearch.WordTrace tailWord_4656546 prefixEnd_4656546 797015429257081158686647 := by
  unfold tailWord_4656546
  simp only [CollatzResearch.WordTrace]
  refine ⟨42459546347034147896713373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113225456925424394391235661 42459546347034147896713373)
  ·
    refine ⟨15922329880137805461267515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42459546347034147896713373 15922329880137805461267515)
    ·
      refine ⟨23883494820206708191901273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15922329880137805461267515 23883494820206708191901273)
      ·
        refine ⟨17912621115155031143925955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23883494820206708191901273 17912621115155031143925955)
        ·
          refine ⟨26868931672732546715888933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17912621115155031143925955 26868931672732546715888933)
          ·
            refine ⟨5037924688637352509229175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26868931672732546715888933 5037924688637352509229175)
            ·
              refine ⟨7556887032956028763843763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5037924688637352509229175 7556887032956028763843763)
              ·
                refine ⟨11335330549434043145765645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7556887032956028763843763 11335330549434043145765645)
                ·
                  refine ⟨4250748956037766179662117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11335330549434043145765645 4250748956037766179662117)
                  ·
                    refine ⟨797015429257081158686647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250748956037766179662117 797015429257081158686647)
                    ·
                      rfl

theorem cell23_4656546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_4656546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656546 prefixEnd_4656546 := by exact prefixLift 4656546
  have htrace : WordTrace (prefixWord ++ tailWord_4656546) baseStart_4656546 baseEnd_4656546 := by
    simpa [prefixWord, tailWord_4656546, baseEnd_4656546] using wordTrace_append hprefix tailTrace_4656546
  have hstable : (prefixWord ++ tailWord_4656546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656546).length < 2 ^ (prefixWord ++ tailWord_4656546).sum := by decide
  have hdescent : baseEnd_4656546 < baseStart_4656546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656579 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 2, 3, 2]
def baseStart_4656579 : Nat := 118140960795 + 4656579 * 2 ^ 59
def prefixEnd_4656579 : Nat := 4983230072969 + 3 ^ 40 * 4656579 * 2
def baseEnd_4656579 : Nat := 2391063232632841846947289

theorem tailTrace_4656579 : CollatzResearch.WordTrace tailWord_4656579 prefixEnd_4656579 2391063232632841846947289 := by
  unfold tailWord_4656579
  simp only [CollatzResearch.WordTrace]
  refine ⟨169839388997017038222804791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113226259331344692148536527 169839388997017038222804791)
  ·
    refine ⟨254759083495525557334207187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169839388997017038222804791 254759083495525557334207187)
    ·
      refine ⟨382138625243288336001310781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254759083495525557334207187 382138625243288336001310781)
      ·
        refine ⟨143301984466233126000491543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382138625243288336001310781 143301984466233126000491543)
        ·
          refine ⟨214952976699349689000737315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143301984466233126000491543 214952976699349689000737315)
          ·
            refine ⟨322429465049024533501105973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214952976699349689000737315 322429465049024533501105973)
            ·
              refine ⟨30227762348346050015728685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322429465049024533501105973 30227762348346050015728685)
              ·
                refine ⟨11335410880629768755898257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30227762348346050015728685 11335410880629768755898257)
                ·
                  refine ⟨8501558160472326566923693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11335410880629768755898257 8501558160472326566923693)
                  ·
                    refine ⟨3188084310177122462596385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8501558160472326566923693 3188084310177122462596385)
                    ·
                      refine ⟨2391063232632841846947289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188084310177122462596385 2391063232632841846947289)
                      ·
                        rfl

theorem cell23_4656579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_4656579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656579 prefixEnd_4656579 := by exact prefixLift 4656579
  have htrace : WordTrace (prefixWord ++ tailWord_4656579) baseStart_4656579 baseEnd_4656579 := by
    simpa [prefixWord, tailWord_4656579, baseEnd_4656579] using wordTrace_append hprefix tailTrace_4656579
  have hstable : (prefixWord ++ tailWord_4656579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656579).length < 2 ^ (prefixWord ++ tailWord_4656579).sum := by decide
  have hdescent : baseEnd_4656579 < baseStart_4656579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_4656612 : Nat := 118140960795 + 4656612 * 2 ^ 59
def prefixEnd_4656612 : Nat := 4983230072969 + 3 ^ 40 * 4656612 * 2
def baseEnd_4656612 : Nat := 2391080177494440217834637

theorem tailTrace_4656612 : CollatzResearch.WordTrace tailWord_4656612 prefixEnd_4656612 2391080177494440217834637 := by
  unfold tailWord_4656612
  simp only [CollatzResearch.WordTrace]
  refine ⟨84920296302948742429378045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113227061737264989905837393 84920296302948742429378045)
  ·
    refine ⟨31845111113605778411016767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84920296302948742429378045 31845111113605778411016767)
    ·
      refine ⟨47767666670408667616525151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31845111113605778411016767 47767666670408667616525151)
      ·
        refine ⟨71651500005613001424787727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47767666670408667616525151 71651500005613001424787727)
        ·
          refine ⟨107477250008419502137181591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71651500005613001424787727 107477250008419502137181591)
          ·
            refine ⟨161215875012629253205772387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107477250008419502137181591 161215875012629253205772387)
            ·
              refine ⟨241823812518943879808658581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161215875012629253205772387 241823812518943879808658581)
              ·
                refine ⟨11335491211825494366030871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 241823812518943879808658581 11335491211825494366030871)
                ·
                  refine ⟨17003236817738241549046307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11335491211825494366030871 17003236817738241549046307)
                  ·
                    refine ⟨25504855226607362323569461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17003236817738241549046307 25504855226607362323569461)
                    ·
                      refine ⟨2391080177494440217834637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25504855226607362323569461 2391080177494440217834637)
                      ·
                        rfl

theorem cell23_4656612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_4656612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656612 prefixEnd_4656612 := by exact prefixLift 4656612
  have htrace : WordTrace (prefixWord ++ tailWord_4656612) baseStart_4656612 baseEnd_4656612 := by
    simpa [prefixWord, tailWord_4656612, baseEnd_4656612] using wordTrace_append hprefix tailTrace_4656612
  have hstable : (prefixWord ++ tailWord_4656612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656612).length < 2 ^ (prefixWord ++ tailWord_4656612).sum := by decide
  have hdescent : baseEnd_4656612 < baseStart_4656612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656694 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_4656694 : Nat := 118140960795 + 4656694 * 2 ^ 59
def prefixEnd_4656694 : Nat := 4983230072969 + 3 ^ 40 * 4656694 * 2
def baseEnd_4656694 : Nat := 2391122282908108897009261

theorem tailTrace_4656694 : CollatzResearch.WordTrace tailWord_4656694 prefixEnd_4656694 2391122282908108897009261 := by
  unfold tailWord_4656694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615223961975025803952571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113229055594400275242160757 10615223961975025803952571)
  ·
    refine ⟨15922835942962538705928857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10615223961975025803952571 15922835942962538705928857)
    ·
      refine ⟨11942126957221904029446643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15922835942962538705928857 11942126957221904029446643)
      ·
        refine ⟨17913190435832856044169965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11942126957221904029446643 17913190435832856044169965)
        ·
          refine ⟨6717446413437321016563737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17913190435832856044169965 6717446413437321016563737)
          ·
            refine ⟨5038084810077990762422803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6717446413437321016563737 5038084810077990762422803)
            ·
              refine ⟨7557127215116986143634205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038084810077990762422803 7557127215116986143634205)
              ·
                refine ⟨2833922705668869803862827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7557127215116986143634205 2833922705668869803862827)
                ·
                  refine ⟨4250884058503304705794241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833922705668869803862827 4250884058503304705794241)
                  ·
                    refine ⟨3188163043877478529345681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250884058503304705794241 3188163043877478529345681)
                    ·
                      refine ⟨2391122282908108897009261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188163043877478529345681 2391122282908108897009261)
                      ·
                        rfl

theorem cell23_4656694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_4656694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656694 prefixEnd_4656694 := by exact prefixLift 4656694
  have htrace : WordTrace (prefixWord ++ tailWord_4656694) baseStart_4656694 baseEnd_4656694 := by
    simpa [prefixWord, tailWord_4656694, baseEnd_4656694] using wordTrace_append hprefix tailTrace_4656694
  have hstable : (prefixWord ++ tailWord_4656694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656694).length < 2 ^ (prefixWord ++ tailWord_4656694).sum := by decide
  have hdescent : baseEnd_4656694 < baseStart_4656694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656789 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_4656789 : Nat := 118140960795 + 4656789 * 2 ^ 59
def prefixEnd_4656789 : Nat := 4983230072969 + 3 ^ 40 * 4656789 * 2
def baseEnd_4656789 : Nat := 2391171063570286025321323

theorem tailTrace_4656789 : CollatzResearch.WordTrace tailWord_4656789 prefixEnd_4656789 2391171063570286025321323 := by
  unfold tailWord_4656789
  simp only [CollatzResearch.WordTrace]
  refine ⟨169847048326256244087949421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113231365550837496058632947 169847048326256244087949421)
  ·
    refine ⟨63692643122346091532981033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169847048326256244087949421 63692643122346091532981033)
    ·
      refine ⟨47769482341759568649735775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63692643122346091532981033 47769482341759568649735775)
      ·
        refine ⟨71654223512639352974603663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47769482341759568649735775 71654223512639352974603663)
        ·
          refine ⟨107481335268959029461905495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71654223512639352974603663 107481335268959029461905495)
          ·
            refine ⟨161222002903438544192858243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107481335268959029461905495 161222002903438544192858243)
            ·
              refine ⟨241833004355157816289287365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161222002903438544192858243 241833004355157816289287365)
              ·
                refine ⟨45343688316592090554241381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241833004355157816289287365 45343688316592090554241381)
                ·
                  refine ⟨8501941559361016978920259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45343688316592090554241381 8501941559361016978920259)
                  ·
                    refine ⟨12752912339041525468380389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8501941559361016978920259 12752912339041525468380389)
                    ·
                      refine ⟨2391171063570286025321323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12752912339041525468380389 2391171063570286025321323)
                      ·
                        rfl

theorem cell23_4656789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_4656789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656789 prefixEnd_4656789 := by exact prefixLift 4656789
  have htrace : WordTrace (prefixWord ++ tailWord_4656789) baseStart_4656789 baseEnd_4656789 := by
    simpa [prefixWord, tailWord_4656789, baseEnd_4656789] using wordTrace_append hprefix tailTrace_4656789
  have hstable : (prefixWord ++ tailWord_4656789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656789).length < 2 ^ (prefixWord ++ tailWord_4656789).sum := by decide
  have hdescent : baseEnd_4656789 < baseStart_4656789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656829 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 8]
def baseStart_4656829 : Nat := 118140960795 + 4656829 * 2 ^ 59
def prefixEnd_4656829 : Nat := 4983230072969 + 3 ^ 40 * 4656829 * 2
def baseEnd_4656829 : Nat := 265687955866273985424571

theorem tailTrace_4656829 : CollatzResearch.WordTrace tailWord_4656829 prefixEnd_4656829 265687955866273985424571 := by
  unfold tailWord_4656829
  simp only [CollatzResearch.WordTrace]
  refine ⟨169848507246111330919405541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113232338164074220612937027 169848507246111330919405541)
  ·
    refine ⟨31846595108645874547388539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169848507246111330919405541 31846595108645874547388539)
    ·
      refine ⟨47769892662968811821082809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31846595108645874547388539 47769892662968811821082809)
      ·
        refine ⟨35827419497226608865812107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47769892662968811821082809 35827419497226608865812107)
        ·
          refine ⟨53741129245839913298718161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35827419497226608865812107 53741129245839913298718161)
          ·
            refine ⟨40305846934379934974038621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53741129245839913298718161 40305846934379934974038621)
            ·
              refine ⟨15114692600392475615264483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40305846934379934974038621 15114692600392475615264483)
              ·
                refine ⟨22672038900588713422896725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15114692600392475615264483 22672038900588713422896725)
                ·
                  refine ⟨265687955866273985424571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22672038900588713422896725 265687955866273985424571)
                  ·
                    rfl

theorem cell23_4656829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_4656829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656829 prefixEnd_4656829 := by exact prefixLift 4656829
  have htrace : WordTrace (prefixWord ++ tailWord_4656829) baseStart_4656829 baseEnd_4656829 := by
    simpa [prefixWord, tailWord_4656829, baseEnd_4656829] using wordTrace_append hprefix tailTrace_4656829
  have hstable : (prefixWord ++ tailWord_4656829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656829).length < 2 ^ (prefixWord ++ tailWord_4656829).sum := by decide
  have hdescent : baseEnd_4656829 < baseStart_4656829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656867 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 1, 4]
def baseStart_4656867 : Nat := 118140960795 + 4656867 * 2 ^ 59
def prefixEnd_4656867 : Nat := 4983230072969 + 3 ^ 40 * 4656867 * 2
def baseEnd_4656867 : Nat := 797070371687112240048655

theorem tailTrace_4656867 : CollatzResearch.WordTrace tailWord_4656867 prefixEnd_4656867 797070371687112240048655 := by
  unfold tailWord_4656867
  simp only [CollatzResearch.WordTrace]
  refine ⟨169849893219973663409288855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113233262146649108939525903 169849893219973663409288855)
  ·
    refine ⟨254774839829960495113933283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169849893219973663409288855 254774839829960495113933283)
    ·
      refine ⟨382162259744940742670899925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254774839829960495113933283 382162259744940742670899925)
      ·
        refine ⟨8956927962772048656349217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 382162259744940742670899925 8956927962772048656349217)
        ·
          refine ⟨6717695972079036492261913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8956927962772048656349217 6717695972079036492261913)
          ·
            refine ⟨5038271979059277369196435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6717695972079036492261913 5038271979059277369196435)
            ·
              refine ⟨7557407968588916053794653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038271979059277369196435 7557407968588916053794653)
              ·
                refine ⟨2834027988220843520172995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7557407968588916053794653 2834027988220843520172995)
                ·
                  refine ⟨4251041982331265280259493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834027988220843520172995 4251041982331265280259493)
                  ·
                    refine ⟨797070371687112240048655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251041982331265280259493 797070371687112240048655)
                    ·
                      rfl

theorem cell23_4656867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 4].length) (baseStart_4656867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656867 prefixEnd_4656867 := by exact prefixLift 4656867
  have htrace : WordTrace (prefixWord ++ tailWord_4656867) baseStart_4656867 baseEnd_4656867 := by
    simpa [prefixWord, tailWord_4656867, baseEnd_4656867] using wordTrace_append hprefix tailTrace_4656867
  have hstable : (prefixWord ++ tailWord_4656867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656867).length < 2 ^ (prefixWord ++ tailWord_4656867).sum := by decide
  have hdescent : baseEnd_4656867 < baseStart_4656867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656876 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_4656876 : Nat := 118140960795 + 4656876 * 2 ^ 59
def prefixEnd_4656876 : Nat := 4983230072969 + 3 ^ 40 * 4656876 * 2
def baseEnd_4656876 : Nat := 797071912129075728311141

theorem tailTrace_4656876 : CollatzResearch.WordTrace tailWord_4656876 prefixEnd_4656876 797071912129075728311141 := by
  unfold tailWord_4656876
  simp only [CollatzResearch.WordTrace]
  refine ⟨84925110738470528973183241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113233480984627371964244321 84925110738470528973183241)
  ·
    refine ⟨63693833053852896729887431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84925110738470528973183241 63693833053852896729887431)
    ·
      refine ⟨95540749580779345094831147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63693833053852896729887431 95540749580779345094831147)
      ·
        refine ⟨143311124371169017642246721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95540749580779345094831147 143311124371169017642246721)
        ·
          refine ⟨107483343278376763231685041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143311124371169017642246721 107483343278376763231685041)
          ·
            refine ⟨80612507458782572423763781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107483343278376763231685041 80612507458782572423763781)
            ·
              refine ⟨15114845148521732329455709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80612507458782572423763781 15114845148521732329455709)
              ·
                refine ⟨5668066930695649623545891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15114845148521732329455709 5668066930695649623545891)
                ·
                  refine ⟨8502100396043474435318837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5668066930695649623545891 8502100396043474435318837)
                  ·
                    refine ⟨797071912129075728311141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8502100396043474435318837 797071912129075728311141)
                    ·
                      rfl

theorem cell23_4656876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_4656876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656876 prefixEnd_4656876 := by exact prefixLift 4656876
  have htrace : WordTrace (prefixWord ++ tailWord_4656876) baseStart_4656876 baseEnd_4656876 := by
    simpa [prefixWord, tailWord_4656876, baseEnd_4656876] using wordTrace_append hprefix tailTrace_4656876
  have hstable : (prefixWord ++ tailWord_4656876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656876).length < 2 ^ (prefixWord ++ tailWord_4656876).sum := by decide
  have hdescent : baseEnd_4656876 < baseStart_4656876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656913 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 5, 2, 2]
def baseStart_4656913 : Nat := 118140960795 + 4656913 * 2 ^ 59
def prefixEnd_4656913 : Nat := 4983230072969 + 3 ^ 40 * 4656913 * 2
def baseEnd_4656913 : Nat := 2391234735171443540170753

theorem tailTrace_4656913 : CollatzResearch.WordTrace tailWord_4656913 prefixEnd_4656913 2391234735171443540170753 := by
  unfold tailWord_4656913
  simp only [CollatzResearch.WordTrace]
  refine ⟨169851570977807013265463393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113234380651871342176975595 169851570977807013265463393)
  ·
    refine ⟨127388678233355259949097545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169851570977807013265463393 127388678233355259949097545)
    ·
      refine ⟨95541508675016444961823159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127388678233355259949097545 95541508675016444961823159)
      ·
        refine ⟨143312263012524667442734739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95541508675016444961823159 143312263012524667442734739)
        ·
          refine ⟨214968394518787001164102109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143312263012524667442734739 214968394518787001164102109)
          ·
            refine ⟨80613147944545125436538291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214968394518787001164102109 80613147944545125436538291)
            ·
              refine ⟨120919721916817688154807437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80613147944545125436538291 120919721916817688154807437)
              ·
                refine ⟨45344895718806633058052789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120919721916817688154807437 45344895718806633058052789)
                ·
                  refine ⟨4251083973638121849192449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45344895718806633058052789 4251083973638121849192449)
                  ·
                    refine ⟨3188312980228591386894337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4251083973638121849192449 3188312980228591386894337)
                    ·
                      refine ⟨2391234735171443540170753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188312980228591386894337 2391234735171443540170753)
                      ·
                        rfl

theorem cell23_4656913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_4656913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656913 prefixEnd_4656913 := by exact prefixLift 4656913
  have htrace : WordTrace (prefixWord ++ tailWord_4656913) baseStart_4656913 baseEnd_4656913 := by
    simpa [prefixWord, tailWord_4656913, baseEnd_4656913] using wordTrace_append hprefix tailTrace_4656913
  have hstable : (prefixWord ++ tailWord_4656913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656913).length < 2 ^ (prefixWord ++ tailWord_4656913).sum := by decide
  have hdescent : baseEnd_4656913 < baseStart_4656913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656930 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_4656930 : Nat := 118140960795 + 4656930 * 2 ^ 59
def prefixEnd_4656930 : Nat := 4983230072969 + 3 ^ 40 * 4656930 * 2
def baseEnd_4656930 : Nat := 2391243464342569973658175

theorem tailTrace_4656930 : CollatzResearch.WordTrace tailWord_4656930 prefixEnd_4656930 2391243464342569973658175 := by
  unfold tailWord_4656930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42463047754686356292208061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113234794012496950112554829 42463047754686356292208061)
  ·
    refine ⟨15923642908007383609578023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42463047754686356292208061 15923642908007383609578023)
    ·
      refine ⟨23885464362011075414367035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15923642908007383609578023 23885464362011075414367035)
      ·
        refine ⟨35828196543016613121550553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23885464362011075414367035 35828196543016613121550553)
        ·
          refine ⟨26871147407262459841162915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35828196543016613121550553 26871147407262459841162915)
          ·
            refine ⟨40306721110893689761744373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26871147407262459841162915 40306721110893689761744373)
            ·
              refine ⟨3778755104146283415163535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40306721110893689761744373 3778755104146283415163535)
              ·
                refine ⟨5668132656219425122745303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778755104146283415163535 5668132656219425122745303)
                ·
                  refine ⟨8502198984329137684117955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5668132656219425122745303 8502198984329137684117955)
                  ·
                    refine ⟨12753298476493706526176933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8502198984329137684117955 12753298476493706526176933)
                    ·
                      refine ⟨2391243464342569973658175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12753298476493706526176933 2391243464342569973658175)
                      ·
                        rfl

theorem cell23_4656930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_4656930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656930 prefixEnd_4656930 := by exact prefixLift 4656930
  have htrace : WordTrace (prefixWord ++ tailWord_4656930) baseStart_4656930 baseEnd_4656930 := by
    simpa [prefixWord, tailWord_4656930, baseEnd_4656930] using wordTrace_append hprefix tailTrace_4656930
  have hstable : (prefixWord ++ tailWord_4656930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656930).length < 2 ^ (prefixWord ++ tailWord_4656930).sum := by decide
  have hdescent : baseEnd_4656930 < baseStart_4656930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656933 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_4656933 : Nat := 118140960795 + 4656933 * 2 ^ 59
def prefixEnd_4656933 : Nat := 4983230072969 + 3 ^ 40 * 4656933 * 2
def baseEnd_4656933 : Nat := 2391245004784533461920661

theorem tailTrace_4656933 : CollatzResearch.WordTrace tailWord_4656933 prefixEnd_4656933 2391245004784533461920661 := by
  unfold tailWord_4656933
  simp only [CollatzResearch.WordTrace]
  refine ⟨169852300437734556681191453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113234866958489704454127635 169852300437734556681191453)
  ·
    refine ⟨63694612664150458755446795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169852300437734556681191453 63694612664150458755446795)
    ·
      refine ⟨95541918996225688133170193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63694612664150458755446795 95541918996225688133170193)
      ·
        refine ⟨71656439247169266099877645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95541918996225688133170193 71656439247169266099877645)
        ·
          refine ⟨26871164717688474787454117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71656439247169266099877645 26871164717688474787454117)
          ·
            refine ⟨5038343384566589022647647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26871164717688474787454117 5038343384566589022647647)
            ·
              refine ⟨7557515076849883533971471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038343384566589022647647 7557515076849883533971471)
              ·
                refine ⟨11336272615274825300957207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557515076849883533971471 11336272615274825300957207)
                ·
                  refine ⟨17004408922912237951435811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11336272615274825300957207 17004408922912237951435811)
                  ·
                    refine ⟨25506613384368356927153717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17004408922912237951435811 25506613384368356927153717)
                    ·
                      refine ⟨2391245004784533461920661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25506613384368356927153717 2391245004784533461920661)
                      ·
                        rfl

theorem cell23_4656933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_4656933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656933 prefixEnd_4656933 := by exact prefixLift 4656933
  have htrace : WordTrace (prefixWord ++ tailWord_4656933) baseStart_4656933 baseEnd_4656933 := by
    simpa [prefixWord, tailWord_4656933, baseEnd_4656933] using wordTrace_append hprefix tailTrace_4656933
  have hstable : (prefixWord ++ tailWord_4656933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656933).length < 2 ^ (prefixWord ++ tailWord_4656933).sum := by decide
  have hdescent : baseEnd_4656933 < baseStart_4656933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656950 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4656950 : Nat := 118140960795 + 4656950 * 2 ^ 59
def prefixEnd_4656950 : Nat := 4983230072969 + 3 ^ 40 * 4656950 * 2
def baseEnd_4656950 : Nat := 2391253733955659895408083

theorem tailTrace_4656950 : CollatzResearch.WordTrace tailWord_4656950 prefixEnd_4656950 2391253733955659895408083 := by
  unfold tailWord_4656950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615807529917060536535019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113235280319115312389706869 10615807529917060536535019)
  ·
    refine ⟨15923711294875590804802529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10615807529917060536535019 15923711294875590804802529)
    ·
      refine ⟨11942783471156693103601897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15923711294875590804802529 11942783471156693103601897)
      ·
        refine ⟨8957087603367519827701423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11942783471156693103601897 8957087603367519827701423)
        ·
          refine ⟨13435631405051279741552135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8957087603367519827701423 13435631405051279741552135)
          ·
            refine ⟨20153447107576919612328203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13435631405051279741552135 20153447107576919612328203)
            ·
              refine ⟨30230170661365379418492305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20153447107576919612328203 30230170661365379418492305)
              ·
                refine ⟨22672627996024034563869229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30230170661365379418492305 22672627996024034563869229)
                ·
                  refine ⟨8502235498509012961450961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22672627996024034563869229 8502235498509012961450961)
                  ·
                    refine ⟨6376676623881759721088221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8502235498509012961450961 6376676623881759721088221)
                    ·
                      refine ⟨2391253733955659895408083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6376676623881759721088221 2391253733955659895408083)
                      ·
                        rfl

theorem cell23_4656950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4656950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656950 prefixEnd_4656950 := by exact prefixLift 4656950
  have htrace : WordTrace (prefixWord ++ tailWord_4656950) baseStart_4656950 baseEnd_4656950 := by
    simpa [prefixWord, tailWord_4656950, baseEnd_4656950] using wordTrace_append hprefix tailTrace_4656950
  have hstable : (prefixWord ++ tailWord_4656950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656950).length < 2 ^ (prefixWord ++ tailWord_4656950).sum := by decide
  have hdescent : baseEnd_4656950 < baseStart_4656950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4656963 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 3]
def baseStart_4656963 : Nat := 118140960795 + 4656963 * 2 ^ 59
def prefixEnd_4656963 : Nat := 4983230072969 + 3 ^ 40 * 4656963 * 2
def baseEnd_4656963 : Nat := 2391260409204168344545523

theorem tailTrace_4656963 : CollatzResearch.WordTrace tailWord_4656963 prefixEnd_4656963 2391260409204168344545523 := by
  unfold tailWord_4656963
  simp only [CollatzResearch.WordTrace]
  refine ⟨169853394627625871804783543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113235596418417247869855695 169853394627625871804783543)
  ·
    refine ⟨254780091941438807707175315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169853394627625871804783543 254780091941438807707175315)
    ·
      refine ⟨382170137912158211560762973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254780091941438807707175315 382170137912158211560762973)
      ·
        refine ⟨143313801717059329335286115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382170137912158211560762973 143313801717059329335286115)
        ·
          refine ⟨214970702575588994002929173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143313801717059329335286115 214970702575588994002929173)
          ·
            refine ⟨10076751683230734093887305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 214970702575588994002929173 10076751683230734093887305)
            ·
              refine ⟨7557563762423050570415479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10076751683230734093887305 7557563762423050570415479)
              ·
                refine ⟨11336345643634575855623219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557563762423050570415479 11336345643634575855623219)
                ·
                  refine ⟨17004518465451863783434829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11336345643634575855623219 17004518465451863783434829)
                  ·
                    refine ⟨6376694424544448918788061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17004518465451863783434829 6376694424544448918788061)
                    ·
                      refine ⟨2391260409204168344545523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6376694424544448918788061 2391260409204168344545523)
                      ·
                        rfl

theorem cell23_4656963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_4656963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4656963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4656963 prefixEnd_4656963 := by exact prefixLift 4656963
  have htrace : WordTrace (prefixWord ++ tailWord_4656963) baseStart_4656963 baseEnd_4656963 := by
    simpa [prefixWord, tailWord_4656963, baseEnd_4656963] using wordTrace_append hprefix tailTrace_4656963
  have hstable : (prefixWord ++ tailWord_4656963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4656963).length < 2 ^ (prefixWord ++ tailWord_4656963).sum := by decide
  have hdescent : baseEnd_4656963 < baseStart_4656963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4656963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657014 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4657014 : Nat := 118140960795 + 4657014 * 2 ^ 59
def prefixEnd_4657014 : Nat := 4983230072969 + 3 ^ 40 * 4657014 * 2
def baseEnd_4657014 : Nat := 2391286596717547645007789

theorem tailTrace_4657014 : CollatzResearch.WordTrace tailWord_4657014 prefixEnd_4657014 2391286596717547645007789 := by
  unfold tailWord_4657014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615953421902569219680631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113236836500294071676593397 10615953421902569219680631)
  ·
    refine ⟨15923930132853853829520947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10615953421902569219680631 15923930132853853829520947)
    ·
      refine ⟨23885895199280780744281421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15923930132853853829520947 23885895199280780744281421)
      ·
        refine ⟨8957210699730292779105533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23885895199280780744281421 8957210699730292779105533)
        ·
          refine ⟨3358954012398859792164575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8957210699730292779105533 3358954012398859792164575)
          ·
            refine ⟨5038431018598289688246863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358954012398859792164575 5038431018598289688246863)
            ·
              refine ⟨7557646527897434532370295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038431018598289688246863 7557646527897434532370295)
              ·
                refine ⟨11336469791846151798555443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557646527897434532370295 11336469791846151798555443)
                ·
                  refine ⟨17004704687769227697833165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11336469791846151798555443 17004704687769227697833165)
                  ·
                    refine ⟨6376764257913460386687437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17004704687769227697833165 6376764257913460386687437)
                    ·
                      refine ⟨2391286596717547645007789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6376764257913460386687437 2391286596717547645007789)
                      ·
                        rfl

theorem cell23_4657014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4657014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657014 prefixEnd_4657014 := by exact prefixLift 4657014
  have htrace : WordTrace (prefixWord ++ tailWord_4657014) baseStart_4657014 baseEnd_4657014 := by
    simpa [prefixWord, tailWord_4657014, baseEnd_4657014] using wordTrace_append hprefix tailTrace_4657014
  have hstable : (prefixWord ++ tailWord_4657014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657014).length < 2 ^ (prefixWord ++ tailWord_4657014).sum := by decide
  have hdescent : baseEnd_4657014 < baseStart_4657014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657093 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 6, 2]
def baseStart_4657093 : Nat := 118140960795 + 4657093 * 2 ^ 59
def prefixEnd_4657093 : Nat := 4983230072969 + 3 ^ 40 * 4657093 * 2
def baseEnd_4657093 : Nat := 2391327161689252835919925

theorem tailTrace_4657093 : CollatzResearch.WordTrace tailWord_4657093 prefixEnd_4657093 2391327161689252835919925 := by
  unfold tailWord_4657093
  simp only [CollatzResearch.WordTrace]
  refine ⟨169858136117154904007015933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113238757411436602671343955 169858136117154904007015933)
  ·
    refine ⟨63696801043933089002630975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169858136117154904007015933 63696801043933089002630975)
    ·
      refine ⟨95545201565899633503946463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63696801043933089002630975 95545201565899633503946463)
      ·
        refine ⟨143317802348849450255919695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95545201565899633503946463 143317802348849450255919695)
        ·
          refine ⟨214976703523274175383879543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143317802348849450255919695 214976703523274175383879543)
          ·
            refine ⟨322465055284911263075819315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214976703523274175383879543 322465055284911263075819315)
            ·
              refine ⟨483697582927366894613728973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322465055284911263075819315 483697582927366894613728973)
              ·
                refine ⟨181386593597762585480148365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483697582927366894613728973 181386593597762585480148365)
                ·
                  refine ⟨68019972599160969555055637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181386593597762585480148365 68019972599160969555055637)
                  ·
                    refine ⟨3188436215585670447893233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68019972599160969555055637 3188436215585670447893233)
                    ·
                      refine ⟨2391327161689252835919925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188436215585670447893233 2391327161689252835919925)
                      ·
                        rfl

theorem cell23_4657093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_4657093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657093 prefixEnd_4657093 := by exact prefixLift 4657093
  have htrace : WordTrace (prefixWord ++ tailWord_4657093) baseStart_4657093 baseEnd_4657093 := by
    simpa [prefixWord, tailWord_4657093, baseEnd_4657093] using wordTrace_append hprefix tailTrace_4657093
  have hstable : (prefixWord ++ tailWord_4657093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657093).length < 2 ^ (prefixWord ++ tailWord_4657093).sum := by decide
  have hdescent : baseEnd_4657093 < baseStart_4657093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657127 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_4657127 : Nat := 118140960795 + 4657127 * 2 ^ 59
def prefixEnd_4657127 : Nat := 4983230072969 + 3 ^ 40 * 4657127 * 2
def baseEnd_4657127 : Nat := 2391344620031505702894769

theorem tailTrace_4657127 : CollatzResearch.WordTrace tailWord_4657127 prefixEnd_4657127 2391344620031505702894769 := by
  unfold tailWord_4657127
  simp only [CollatzResearch.WordTrace]
  refine ⟨169859376199031727813753635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113239584132687818542502423 169859376199031727813753635)
  ·
    refine ⟨254789064298547591720630453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169859376199031727813753635 254789064298547591720630453)
    ·
      refine ⟨23886474777988836723809105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254789064298547591720630453 23886474777988836723809105)
      ·
        refine ⟨17914856083491627542856829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23886474777988836723809105 17914856083491627542856829)
        ·
          refine ⟨6718071031309360328571311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17914856083491627542856829 6718071031309360328571311)
          ·
            refine ⟨10077106546964040492856967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718071031309360328571311 10077106546964040492856967)
            ·
              refine ⟨15115659820446060739285451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10077106546964040492856967 15115659820446060739285451)
              ·
                refine ⟨22673489730669091108928177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15115659820446060739285451 22673489730669091108928177)
                ·
                  refine ⟨17005117298001818331696133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22673489730669091108928177 17005117298001818331696133)
                  ·
                    refine ⟨3188459493375340937193025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17005117298001818331696133 3188459493375340937193025)
                    ·
                      refine ⟨2391344620031505702894769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188459493375340937193025 2391344620031505702894769)
                      ·
                        rfl

theorem cell23_4657127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_4657127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657127 prefixEnd_4657127 := by exact prefixLift 4657127
  have htrace : WordTrace (prefixWord ++ tailWord_4657127) baseStart_4657127 baseEnd_4657127 := by
    simpa [prefixWord, tailWord_4657127, baseEnd_4657127] using wordTrace_append hprefix tailTrace_4657127
  have hstable : (prefixWord ++ tailWord_4657127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657127).length < 2 ^ (prefixWord ++ tailWord_4657127).sum := by decide
  have hdescent : baseEnd_4657127 < baseStart_4657127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657160 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_4657160 : Nat := 118140960795 + 4657160 * 2 ^ 59
def prefixEnd_4657160 : Nat := 4983230072969 + 3 ^ 40 * 4657160 * 2
def baseEnd_4657160 : Nat := 2391361564893104073782117

theorem tailTrace_4657160 : CollatzResearch.WordTrace tailWord_4657160 prefixEnd_4657160 2391361564893104073782117 := by
  unfold tailWord_4657160
  simp only [CollatzResearch.WordTrace]
  refine ⟨84930289903956087224852467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113240386538608116299803289 84930289903956087224852467)
  ·
    refine ⟨127395434855934130837278701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84930289903956087224852467 127395434855934130837278701)
    ·
      refine ⟨47773288070975299063979513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127395434855934130837278701 47773288070975299063979513)
      ·
        refine ⟨35829966053231474297984635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47773288070975299063979513 35829966053231474297984635)
        ·
          refine ⟨53744949079847211446976953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35829966053231474297984635 53744949079847211446976953)
          ·
            refine ⟨40308711809885408585232715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53744949079847211446976953 40308711809885408585232715)
            ·
              refine ⟨60463067714828112877849073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40308711809885408585232715 60463067714828112877849073)
              ·
                refine ⟨45347300786121084658386805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60463067714828112877849073 45347300786121084658386805)
                ·
                  refine ⟨4251309448698851686723763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45347300786121084658386805 4251309448698851686723763)
                  ·
                    refine ⟨6376964173048277530085645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4251309448698851686723763 6376964173048277530085645)
                    ·
                      refine ⟨2391361564893104073782117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6376964173048277530085645 2391361564893104073782117)
                      ·
                        rfl

theorem cell23_4657160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_4657160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657160 prefixEnd_4657160 := by exact prefixLift 4657160
  have htrace : WordTrace (prefixWord ++ tailWord_4657160) baseStart_4657160 baseEnd_4657160 := by
    simpa [prefixWord, tailWord_4657160, baseEnd_4657160] using wordTrace_append hprefix tailTrace_4657160
  have hstable : (prefixWord ++ tailWord_4657160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657160).length < 2 ^ (prefixWord ++ tailWord_4657160).sum := by decide
  have hdescent : baseEnd_4657160 < baseStart_4657160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657200 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4]
def baseStart_4657200 : Nat := 118140960795 + 4657200 * 2 ^ 59
def prefixEnd_4657200 : Nat := 4983230072969 + 3 ^ 40 * 4657200 * 2
def baseEnd_4657200 : Nat := 2391382104119283917281933

theorem tailTrace_4657200 : CollatzResearch.WordTrace tailWord_4657200 prefixEnd_4657200 2391382104119283917281933 := by
  unfold tailWord_4657200
  simp only [CollatzResearch.WordTrace]
  refine ⟨84931019363883630640580527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113241359151844840854107369 84931019363883630640580527)
  ·
    refine ⟨127396529045825445960870791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84931019363883630640580527 127396529045825445960870791)
    ·
      refine ⟨191094793568738168941306187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127396529045825445960870791 191094793568738168941306187)
      ·
        refine ⟨286642190353107253411959281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191094793568738168941306187 286642190353107253411959281)
        ·
          refine ⟨214981642764830440058969461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286642190353107253411959281 214981642764830440058969461)
          ·
            refine ⟨20154529009202853755528387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214981642764830440058969461 20154529009202853755528387)
            ·
              refine ⟨30231793513804280633292581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20154529009202853755528387 30231793513804280633292581)
              ·
                refine ⟨5668461283838302618742359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30231793513804280633292581 5668461283838302618742359)
                ·
                  refine ⟨8502691925757453928113539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5668461283838302618742359 8502691925757453928113539)
                  ·
                    refine ⟨12754037888636180892170309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8502691925757453928113539 12754037888636180892170309)
                    ·
                      refine ⟨2391382104119283917281933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12754037888636180892170309 2391382104119283917281933)
                      ·
                        rfl

theorem cell23_4657200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_4657200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657200 prefixEnd_4657200 := by exact prefixLift 4657200
  have htrace : WordTrace (prefixWord ++ tailWord_4657200) baseStart_4657200 baseEnd_4657200 := by
    simpa [prefixWord, tailWord_4657200, baseEnd_4657200] using wordTrace_append hprefix tailTrace_4657200
  have hstable : (prefixWord ++ tailWord_4657200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657200).length < 2 ^ (prefixWord ++ tailWord_4657200).sum := by decide
  have hdescent : baseEnd_4657200 < baseStart_4657200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657217 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4657217 : Nat := 118140960795 + 4657217 * 2 ^ 59
def prefixEnd_4657217 : Nat := 4983230072969 + 3 ^ 40 * 4657217 * 2
def baseEnd_4657217 : Nat := 2391390833290410350769355

theorem tailTrace_4657217 : CollatzResearch.WordTrace tailWord_4657217 prefixEnd_4657217 2391390833290410350769355 := by
  unfold tailWord_4657217
  simp only [CollatzResearch.WordTrace]
  refine ⟨169862658768705673184529905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113241772512470448789686603 169862658768705673184529905)
  ·
    refine ⟨127396994076529254888397429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169862658768705673184529905 127396994076529254888397429)
    ·
      refine ⟨11943468194674617645787259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127396994076529254888397429 11943468194674617645787259)
      ·
        refine ⟨17915202292011926468680889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11943468194674617645787259 17915202292011926468680889)
        ·
          refine ⟨13436401719008944851510667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17915202292011926468680889 13436401719008944851510667)
          ·
            refine ⟨20154602578513417277266001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13436401719008944851510667 20154602578513417277266001)
            ·
              refine ⟨15115951933885062957949501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20154602578513417277266001 15115951933885062957949501)
              ·
                refine ⟨5668481975206898609231063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15115951933885062957949501 5668481975206898609231063)
                ·
                  refine ⟨8502722962810347913846595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5668481975206898609231063 8502722962810347913846595)
                  ·
                    refine ⟨12754084444215521870769893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8502722962810347913846595 12754084444215521870769893)
                    ·
                      refine ⟨2391390833290410350769355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12754084444215521870769893 2391390833290410350769355)
                      ·
                        rfl

theorem cell23_4657217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4657217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657217 prefixEnd_4657217 := by exact prefixLift 4657217
  have htrace : WordTrace (prefixWord ++ tailWord_4657217) baseStart_4657217 baseEnd_4657217 := by
    simpa [prefixWord, tailWord_4657217, baseEnd_4657217] using wordTrace_append hprefix tailTrace_4657217
  have hstable : (prefixWord ++ tailWord_4657217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657217).length < 2 ^ (prefixWord ++ tailWord_4657217).sum := by decide
  have hdescent : baseEnd_4657217 < baseStart_4657217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657244 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_4657244 : Nat := 118140960795 + 4657244 * 2 ^ 59
def prefixEnd_4657244 : Nat := 4983230072969 + 3 ^ 40 * 4657244 * 2
def baseEnd_4657244 : Nat := 797134899089360581710577

theorem tailTrace_4657244 : CollatzResearch.WordTrace tailWord_4657244 prefixEnd_4657244 797134899089360581710577 := by
  unfold tailWord_4657244
  simp only [CollatzResearch.WordTrace]
  refine ⟨84931821769803928397881393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113242429026405237863841857 84931821769803928397881393)
  ·
    refine ⟨63698866327352946298411045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84931821769803928397881393 63698866327352946298411045)
    ·
      refine ⟨11943537436378677430952071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63698866327352946298411045 11943537436378677430952071)
      ·
        refine ⟨17915306154568016146428107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11943537436378677430952071 17915306154568016146428107)
        ·
          refine ⟨26872959231852024219642161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17915306154568016146428107 26872959231852024219642161)
          ·
            refine ⟨20154719423889018164731621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26872959231852024219642161 20154719423889018164731621)
            ·
              refine ⟨3779009891979190905887179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20154719423889018164731621 3779009891979190905887179)
              ·
                refine ⟨5668514837968786358830769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779009891979190905887179 5668514837968786358830769)
                ·
                  refine ⟨4251386128476589769123077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668514837968786358830769 4251386128476589769123077)
                  ·
                    refine ⟨797134899089360581710577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251386128476589769123077 797134899089360581710577)
                    ·
                      rfl

theorem cell23_4657244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_4657244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657244 prefixEnd_4657244 := by exact prefixLift 4657244
  have htrace : WordTrace (prefixWord ++ tailWord_4657244) baseStart_4657244 baseEnd_4657244 := by
    simpa [prefixWord, tailWord_4657244, baseEnd_4657244] using wordTrace_append hprefix tailTrace_4657244
  have hstable : (prefixWord ++ tailWord_4657244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657244).length < 2 ^ (prefixWord ++ tailWord_4657244).sum := by decide
  have hdescent : baseEnd_4657244 < baseStart_4657244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657284 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_4657284 : Nat := 118140960795 + 4657284 * 2 ^ 59
def prefixEnd_4657284 : Nat := 4983230072969 + 3 ^ 40 * 4657284 * 2
def baseEnd_4657284 : Nat := 2391425236494261588631547

theorem tailTrace_4657284 : CollatzResearch.WordTrace tailWord_4657284 prefixEnd_4657284 2391425236494261588631547 := by
  unfold tailWord_4657284
  simp only [CollatzResearch.WordTrace]
  refine ⟨84932551229731471813609453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113243401639641962418145937 84932551229731471813609453)
  ·
    refine ⟨31849706711149301930103545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84932551229731471813609453 31849706711149301930103545)
    ·
      refine ⟨23887280033361976447577659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31849706711149301930103545 23887280033361976447577659)
      ·
        refine ⟨35830920050042964671366489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23887280033361976447577659 35830920050042964671366489)
        ·
          refine ⟨26873190037532223503524867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35830920050042964671366489 26873190037532223503524867)
          ·
            refine ⟨40309785056298335255287301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26873190037532223503524867 40309785056298335255287301)
            ·
              refine ⟨7558084698055937860366369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40309785056298335255287301 7558084698055937860366369)
              ·
                refine ⟨5668563523541953395274777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7558084698055937860366369 5668563523541953395274777)
                ·
                  refine ⟨4251422642656465046456083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668563523541953395274777 4251422642656465046456083)
                  ·
                    refine ⟨6377133963984697569684125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4251422642656465046456083 6377133963984697569684125)
                    ·
                      refine ⟨2391425236494261588631547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6377133963984697569684125 2391425236494261588631547)
                      ·
                        rfl

theorem cell23_4657284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_4657284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657284 prefixEnd_4657284 := by exact prefixLift 4657284
  have htrace : WordTrace (prefixWord ++ tailWord_4657284) baseStart_4657284 baseEnd_4657284 := by
    simpa [prefixWord, tailWord_4657284, baseEnd_4657284] using wordTrace_append hprefix tailTrace_4657284
  have hstable : (prefixWord ++ tailWord_4657284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657284).length < 2 ^ (prefixWord ++ tailWord_4657284).sum := by decide
  have hdescent : baseEnd_4657284 < baseStart_4657284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657290 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4657290 : Nat := 118140960795 + 4657290 * 2 ^ 59
def prefixEnd_4657290 : Nat := 4983230072969 + 3 ^ 40 * 4657290 * 2
def baseEnd_4657290 : Nat := 2391428317378188565156519

theorem tailTrace_4657290 : CollatzResearch.WordTrace tailWord_4657290 prefixEnd_4657290 2391428317378188565156519 := by
  unfold tailWord_4657290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42466330324360301662984331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113243547531627471101291549 42466330324360301662984331)
  ·
    refine ⟨63699495486540452494476497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42466330324360301662984331 63699495486540452494476497)
    ·
      refine ⟨47774621614905339370857373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63699495486540452494476497 47774621614905339370857373)
      ·
        refine ⟨17915483105589502264071515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47774621614905339370857373 17915483105589502264071515)
        ·
          refine ⟨26873224658384253396107273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17915483105589502264071515 26873224658384253396107273)
          ·
            refine ⟨20154918493788190047080455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26873224658384253396107273 20154918493788190047080455)
            ·
              refine ⟨30232377740682285070620683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20154918493788190047080455 30232377740682285070620683)
              ·
                refine ⟨45348566611023427605931025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30232377740682285070620683 45348566611023427605931025)
                ·
                  refine ⟨34011424958267570704448269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45348566611023427605931025 34011424958267570704448269)
                  ·
                    refine ⟨12754284359350339014168101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34011424958267570704448269 12754284359350339014168101)
                    ·
                      refine ⟨2391428317378188565156519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12754284359350339014168101 2391428317378188565156519)
                      ·
                        rfl

theorem cell23_4657290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4657290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657290 prefixEnd_4657290 := by exact prefixLift 4657290
  have htrace : WordTrace (prefixWord ++ tailWord_4657290) baseStart_4657290 baseEnd_4657290 := by
    simpa [prefixWord, tailWord_4657290, baseEnd_4657290] using wordTrace_append hprefix tailTrace_4657290
  have hstable : (prefixWord ++ tailWord_4657290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657290).length < 2 ^ (prefixWord ++ tailWord_4657290).sum := by decide
  have hdescent : baseEnd_4657290 < baseStart_4657290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657302 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4657302 : Nat := 118140960795 + 4657302 * 2 ^ 59
def prefixEnd_4657302 : Nat := 4983230072969 + 3 ^ 40 * 4657302 * 2
def baseEnd_4657302 : Nat := 2391434479146042518206465

theorem tailTrace_4657302 : CollatzResearch.WordTrace tailWord_4657302 prefixEnd_4657302 2391434479146042518206465 := by
  unfold tailWord_4657302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616609935837358293835885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113243839315598488467582773 10616609935837358293835885)
  ·
    refine ⟨3981228725939009360188457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10616609935837358293835885 3981228725939009360188457)
    ·
      refine ⟨2985921544454257020141343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981228725939009360188457 2985921544454257020141343)
      ·
        refine ⟨4478882316681385530212015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985921544454257020141343 4478882316681385530212015)
        ·
          refine ⟨6718323475022078295318023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4478882316681385530212015 6718323475022078295318023)
          ·
            refine ⟨10077485212533117442977035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718323475022078295318023 10077485212533117442977035)
            ·
              refine ⟨15116227818799676164465553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10077485212533117442977035 15116227818799676164465553)
              ·
                refine ⟨11337170864099757123349165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15116227818799676164465553 11337170864099757123349165)
                ·
                  refine ⟨4251439074037408921255937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11337170864099757123349165 4251439074037408921255937)
                  ·
                    refine ⟨3188579305528056690941953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4251439074037408921255937 3188579305528056690941953)
                    ·
                      refine ⟨2391434479146042518206465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188579305528056690941953 2391434479146042518206465)
                      ·
                        rfl

theorem cell23_4657302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4657302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657302 prefixEnd_4657302 := by exact prefixLift 4657302
  have htrace : WordTrace (prefixWord ++ tailWord_4657302) baseStart_4657302 baseEnd_4657302 := by
    simpa [prefixWord, tailWord_4657302, baseEnd_4657302] using wordTrace_append hprefix tailTrace_4657302
  have hstable : (prefixWord ++ tailWord_4657302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657302).length < 2 ^ (prefixWord ++ tailWord_4657302).sum := by decide
  have hdescent : baseEnd_4657302 < baseStart_4657302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657358 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_4657358 : Nat := 118140960795 + 4657358 * 2 ^ 59
def prefixEnd_4657358 : Nat := 4983230072969 + 3 ^ 40 * 4657358 * 2
def baseEnd_4657358 : Nat := 2391463234062694299106207

theorem tailTrace_4657358 : CollatzResearch.WordTrace tailWord_4657358 prefixEnd_4657358 2391463234062694299106207 := by
  unfold tailWord_4657358
  simp only [CollatzResearch.WordTrace]
  refine ⟨21233475182649356783176591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113245200974129902843608485 21233475182649356783176591)
  ·
    refine ⟨31850212773974035174764887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21233475182649356783176591 31850212773974035174764887)
    ·
      refine ⟨47775319160961052762147331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31850212773974035174764887 47775319160961052762147331)
      ·
        refine ⟨71662978741441579143220997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47775319160961052762147331 71662978741441579143220997)
        ·
          refine ⟨13436808514020296089353937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71662978741441579143220997 13436808514020296089353937)
          ·
            refine ⟨10077606385515222067015453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13436808514020296089353937 10077606385515222067015453)
            ·
              refine ⟨3779102394568208275130795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10077606385515222067015453 3779102394568208275130795)
              ·
                refine ⟨5668653591852312412696193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779102394568208275130795 5668653591852312412696193)
                ·
                  refine ⟨4251490193889234309522145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668653591852312412696193 4251490193889234309522145)
                  ·
                    refine ⟨3188617645416925732141609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4251490193889234309522145 3188617645416925732141609)
                    ·
                      refine ⟨2391463234062694299106207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188617645416925732141609 2391463234062694299106207)
                      ·
                        rfl

theorem cell23_4657358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_4657358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657358 prefixEnd_4657358 := by exact prefixLift 4657358
  have htrace : WordTrace (prefixWord ++ tailWord_4657358) baseStart_4657358 baseEnd_4657358 := by
    simpa [prefixWord, tailWord_4657358, baseEnd_4657358] using wordTrace_append hprefix tailTrace_4657358
  have hstable : (prefixWord ++ tailWord_4657358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657358).length < 2 ^ (prefixWord ++ tailWord_4657358).sum := by decide
  have hdescent : baseEnd_4657358 < baseStart_4657358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657487 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 8, 2]
def baseStart_4657487 : Nat := 118140960795 + 4657487 * 2 ^ 59
def prefixEnd_4657487 : Nat := 4983230072969 + 3 ^ 40 * 4657487 * 2
def baseEnd_4657487 : Nat := 2391529473067124294393113

theorem tailTrace_4657487 : CollatzResearch.WordTrace tailWord_4657487 prefixEnd_4657487 2391529473067124294393113 := by
  unfold tailWord_4657487
  simp only [CollatzResearch.WordTrace]
  refine ⟨169872506477727509296858715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113248337651818339531239143 169872506477727509296858715)
  ·
    refine ⟨254808759716591263945288073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169872506477727509296858715 254808759716591263945288073)
    ·
      refine ⟨191106569787443447958966055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254808759716591263945288073 191106569787443447958966055)
      ·
        refine ⟨286659854681165171938449083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191106569787443447958966055 286659854681165171938449083)
        ·
          refine ⟨429989782021747757907673625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286659854681165171938449083 429989782021747757907673625)
          ·
            refine ⟨322492336516310818430755219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429989782021747757907673625 322492336516310818430755219)
            ·
              refine ⟨483738504774466227646132829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322492336516310818430755219 483738504774466227646132829)
              ·
                refine ⟨181401939290424835367299811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483738504774466227646132829 181401939290424835367299811)
                ·
                  refine ⟨272102908935637253050949717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181401939290424835367299811 272102908935637253050949717)
                  ·
                    refine ⟨3188705964089499059190817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 272102908935637253050949717 3188705964089499059190817)
                    ·
                      refine ⟨2391529473067124294393113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188705964089499059190817 2391529473067124294393113)
                      ·
                        rfl

theorem cell23_4657487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8, 2].length) (baseStart_4657487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657487 prefixEnd_4657487 := by exact prefixLift 4657487
  have htrace : WordTrace (prefixWord ++ tailWord_4657487) baseStart_4657487 baseEnd_4657487 := by
    simpa [prefixWord, tailWord_4657487, baseEnd_4657487] using wordTrace_append hprefix tailTrace_4657487
  have hstable : (prefixWord ++ tailWord_4657487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657487).length < 2 ^ (prefixWord ++ tailWord_4657487).sum := by decide
  have hdescent : baseEnd_4657487 < baseStart_4657487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657497 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 4, 4]
def baseStart_4657497 : Nat := 118140960795 + 4657497 * 2 ^ 59
def prefixEnd_4657497 : Nat := 4983230072969 + 3 ^ 40 * 4657497 * 2
def baseEnd_4657497 : Nat := 797178202624556418422689

theorem tailTrace_4657497 : CollatzResearch.WordTrace tailWord_4657497 prefixEnd_4657497 797178202624556418422689 := by
  unfold tailWord_4657497
  simp only [CollatzResearch.WordTrace]
  refine ⟨169872871207691281004722745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113248580805127520669815163 169872871207691281004722745)
  ·
    refine ⟨127404653405768460753542059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169872871207691281004722745 127404653405768460753542059)
    ·
      refine ⟨191106980108652691130313089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127404653405768460753542059 191106980108652691130313089)
      ·
        refine ⟨143330235081489518347734817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191106980108652691130313089 143330235081489518347734817)
        ·
          refine ⟨107497676311117138760801113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143330235081489518347734817 107497676311117138760801113)
          ·
            refine ⟨80623257233337854070600835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107497676311117138760801113 80623257233337854070600835)
            ·
              refine ⟨120934885850006781105901253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80623257233337854070600835 120934885850006781105901253)
              ·
                refine ⟨22675291096876271457356485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120934885850006781105901253 22675291096876271457356485)
                ·
                  refine ⟨4251617080664300898254341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22675291096876271457356485 4251617080664300898254341)
                  ·
                    refine ⟨797178202624556418422689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251617080664300898254341 797178202624556418422689)
                    ·
                      rfl

theorem cell23_4657497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_4657497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657497 prefixEnd_4657497 := by exact prefixLift 4657497
  have htrace : WordTrace (prefixWord ++ tailWord_4657497) baseStart_4657497 baseEnd_4657497 := by
    simpa [prefixWord, tailWord_4657497, baseEnd_4657497] using wordTrace_append hprefix tailTrace_4657497
  have hstable : (prefixWord ++ tailWord_4657497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657497).length < 2 ^ (prefixWord ++ tailWord_4657497).sum := by decide
  have hdescent : baseEnd_4657497 < baseStart_4657497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657507 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4657507 : Nat := 118140960795 + 4657507 * 2 ^ 59
def prefixEnd_4657507 : Nat := 4983230072969 + 3 ^ 40 * 4657507 * 2
def baseEnd_4657507 : Nat := 2391539742680214216143021

theorem tailTrace_4657507 : CollatzResearch.WordTrace tailWord_4657507 prefixEnd_4657507 2391539742680214216143021 := by
  unfold tailWord_4657507
  simp only [CollatzResearch.WordTrace]
  refine ⟨169873235937655052712586775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113248823958436701808391183 169873235937655052712586775)
  ·
    refine ⟨254809853906482579068880163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169873235937655052712586775 254809853906482579068880163)
    ·
      refine ⟨382214780859723868603320245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254809853906482579068880163 382214780859723868603320245)
      ·
        refine ⟨35832635705599112681561273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 382214780859723868603320245 35832635705599112681561273)
        ·
          refine ⟨26874476779199334511170955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35832635705599112681561273 26874476779199334511170955)
          ·
            refine ⟨40311715168799001766756433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26874476779199334511170955 40311715168799001766756433)
            ·
              refine ⟨30233786376599251325067325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40311715168799001766756433 30233786376599251325067325)
              ·
                refine ⟨11337669891224719246900247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30233786376599251325067325 11337669891224719246900247)
                ·
                  refine ⟨17006504836837078870350371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11337669891224719246900247 17006504836837078870350371)
                  ·
                    refine ⟨25509757255255618305525557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17006504836837078870350371 25509757255255618305525557)
                    ·
                      refine ⟨2391539742680214216143021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25509757255255618305525557 2391539742680214216143021)
                      ·
                        rfl

theorem cell23_4657507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4657507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657507 prefixEnd_4657507 := by exact prefixLift 4657507
  have htrace : WordTrace (prefixWord ++ tailWord_4657507) baseStart_4657507 baseEnd_4657507 := by
    simpa [prefixWord, tailWord_4657507, baseEnd_4657507] using wordTrace_append hprefix tailTrace_4657507
  have hstable : (prefixWord ++ tailWord_4657507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657507).length < 2 ^ (prefixWord ++ tailWord_4657507).sum := by decide
  have hdescent : baseEnd_4657507 < baseStart_4657507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657517 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4657517 : Nat := 118140960795 + 4657517 * 2 ^ 59
def prefixEnd_4657517 : Nat := 4983230072969 + 3 ^ 40 * 4657517 * 2
def baseEnd_4657517 : Nat := 2391544877486759177017975

theorem tailTrace_4657517 : CollatzResearch.WordTrace tailWord_4657517 prefixEnd_4657517 2391544877486759177017975 := by
  unfold tailWord_4657517
  simp only [CollatzResearch.WordTrace]
  refine ⟨169873600667618824420450805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113249067111745882946967203 169873600667618824420450805)
  ·
    refine ⟨15925650062589264789417263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169873600667618824420450805 15925650062589264789417263)
    ·
      refine ⟨23888475093883897184125895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15925650062589264789417263 23888475093883897184125895)
      ·
        refine ⟨35832712640825845776188843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23888475093883897184125895 35832712640825845776188843)
        ·
          refine ⟨53749068961238768664283265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35832712640825845776188843 53749068961238768664283265)
          ·
            refine ⟨40311801720929076498212449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53749068961238768664283265 40311801720929076498212449)
            ·
              refine ⟨30233851290696807373659337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40311801720929076498212449 30233851290696807373659337)
              ·
                refine ⟨22675388468022605530244503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30233851290696807373659337 22675388468022605530244503)
                ·
                  refine ⟨34013082702033908295366755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22675388468022605530244503 34013082702033908295366755)
                  ·
                    refine ⟨51019624053050862443050133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34013082702033908295366755 51019624053050862443050133)
                    ·
                      refine ⟨2391544877486759177017975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51019624053050862443050133 2391544877486759177017975)
                      ·
                        rfl

theorem cell23_4657517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4657517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657517 prefixEnd_4657517 := by exact prefixLift 4657517
  have htrace : WordTrace (prefixWord ++ tailWord_4657517) baseStart_4657517 baseEnd_4657517 := by
    simpa [prefixWord, tailWord_4657517, baseEnd_4657517] using wordTrace_append hprefix tailTrace_4657517
  have hstable : (prefixWord ++ tailWord_4657517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657517).length < 2 ^ (prefixWord ++ tailWord_4657517).sum := by decide
  have hdescent : baseEnd_4657517 < baseStart_4657517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657531 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 2, 4]
def baseStart_4657531 : Nat := 118140960795 + 4657531 * 2 ^ 59
def prefixEnd_4657531 : Nat := 4983230072969 + 3 ^ 40 * 4657531 * 2
def baseEnd_4657531 : Nat := 797184022071974040747637

theorem tailTrace_4657531 : CollatzResearch.WordTrace tailWord_4657531 prefixEnd_4657531 797184022071974040747637 := by
  unfold tailWord_4657531
  simp only [CollatzResearch.WordTrace]
  refine ⟨169874111289568104811460447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113249407526378736540973631 169874111289568104811460447)
  ·
    refine ⟨254811166934352157217190671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169874111289568104811460447 254811166934352157217190671)
    ·
      refine ⟨382216750401528235825786007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254811166934352157217190671 382216750401528235825786007)
      ·
        refine ⟨573325125602292353738679011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382216750401528235825786007 573325125602292353738679011)
        ·
          refine ⟨859987688403438530608018517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573325125602292353738679011 859987688403438530608018517)
          ·
            refine ⟨10077980723477795280562717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 859987688403438530608018517 10077980723477795280562717)
            ·
              refine ⟨3779242771304173230211019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10077980723477795280562717 3779242771304173230211019)
              ·
                refine ⟨5668864156956259845316529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779242771304173230211019 5668864156956259845316529)
                ·
                  refine ⟨4251648117717194883987397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668864156956259845316529 4251648117717194883987397)
                  ·
                    refine ⟨797184022071974040747637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251648117717194883987397 797184022071974040747637)
                    ·
                      rfl

theorem cell23_4657531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 4].length) (baseStart_4657531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657531 prefixEnd_4657531 := by exact prefixLift 4657531
  have htrace : WordTrace (prefixWord ++ tailWord_4657531) baseStart_4657531 baseEnd_4657531 := by
    simpa [prefixWord, tailWord_4657531, baseEnd_4657531] using wordTrace_append hprefix tailTrace_4657531
  have hstable : (prefixWord ++ tailWord_4657531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657531).length < 2 ^ (prefixWord ++ tailWord_4657531).sum := by decide
  have hdescent : baseEnd_4657531 < baseStart_4657531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657567 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4657567 : Nat := 118140960795 + 4657567 * 2 ^ 59
def prefixEnd_4657567 : Nat := 4983230072969 + 3 ^ 40 * 4657567 * 2
def baseEnd_4657567 : Nat := 2391570551519483981392745

theorem tailTrace_4657567 : CollatzResearch.WordTrace tailWord_4657567 prefixEnd_4657567 2391570551519483981392745 := by
  unfold tailWord_4657567
  simp only [CollatzResearch.WordTrace]
  refine ⟨169875424317437682959770955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113250282878291788639847303 169875424317437682959770955)
  ·
    refine ⟨254813136476156524439656433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169875424317437682959770955 254813136476156524439656433)
    ·
      refine ⟨191109852357117393329742325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254813136476156524439656433 191109852357117393329742325)
      ·
        refine ⟨17916548658479755624663343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191109852357117393329742325 17916548658479755624663343)
        ·
          refine ⟨26874822987719633436995015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17916548658479755624663343 26874822987719633436995015)
          ·
            refine ⟨40312234481579450155492523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26874822987719633436995015 40312234481579450155492523)
            ·
              refine ⟨60468351722369175233238785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40312234481579450155492523 60468351722369175233238785)
              ·
                refine ⟨45351263791776881424929089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60468351722369175233238785 45351263791776881424929089)
                ·
                  refine ⟨34013447843832661068696817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45351263791776881424929089 34013447843832661068696817)
                  ·
                    refine ⟨25510085882874495801522613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34013447843832661068696817 25510085882874495801522613)
                    ·
                      refine ⟨2391570551519483981392745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25510085882874495801522613 2391570551519483981392745)
                      ·
                        rfl

theorem cell23_4657567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4657567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657567 prefixEnd_4657567 := by exact prefixLift 4657567
  have htrace : WordTrace (prefixWord ++ tailWord_4657567) baseStart_4657567 baseEnd_4657567 := by
    simpa [prefixWord, tailWord_4657567, baseEnd_4657567] using wordTrace_append hprefix tailTrace_4657567
  have hstable : (prefixWord ++ tailWord_4657567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657567).length < 2 ^ (prefixWord ++ tailWord_4657567).sum := by decide
  have hdescent : baseEnd_4657567 < baseStart_4657567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657578 : List Nat := [3, 1, 6, 1, 1, 1, 2, 8]
def baseStart_4657578 : Nat := 118140960795 + 4657578 * 2 ^ 59
def prefixEnd_4657578 : Nat := 4983230072969 + 3 ^ 40 * 4657578 * 2
def baseEnd_4657578 : Nat := 88576896289136423642785

theorem tailTrace_4657578 : CollatzResearch.WordTrace tailWord_4657578 prefixEnd_4657578 88576896289136423642785 := by
  unfold tailWord_4657578
  simp only [CollatzResearch.WordTrace]
  refine ⟨42468956380099457959605347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113250550346931887892280925 42468956380099457959605347)
  ·
    refine ⟨63703434570149186939408021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42468956380099457959605347 63703434570149186939408021)
    ·
      refine ⟨2986098495475743137784751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63703434570149186939408021 2986098495475743137784751)
      ·
        refine ⟨4479147743213614706677127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2986098495475743137784751 4479147743213614706677127)
        ·
          refine ⟨6718721614820422060015691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479147743213614706677127 6718721614820422060015691)
          ·
            refine ⟨10078082422230633090023537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718721614820422060015691 10078082422230633090023537)
            ·
              refine ⟨7558561816672974817517653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10078082422230633090023537 7558561816672974817517653)
              ·
                refine ⟨88576896289136423642785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7558561816672974817517653 88576896289136423642785)
                ·
                  rfl

theorem cell23_4657578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_4657578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657578 prefixEnd_4657578 := by exact prefixLift 4657578
  have htrace : WordTrace (prefixWord ++ tailWord_4657578) baseStart_4657578 baseEnd_4657578 := by
    simpa [prefixWord, tailWord_4657578, baseEnd_4657578] using wordTrace_append hprefix tailTrace_4657578
  have hstable : (prefixWord ++ tailWord_4657578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657578).length < 2 ^ (prefixWord ++ tailWord_4657578).sum := by decide
  have hdescent : baseEnd_4657578 < baseStart_4657578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657594 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2]
def baseStart_4657594 : Nat := 118140960795 + 4657594 * 2 ^ 59
def prefixEnd_4657594 : Nat := 4983230072969 + 3 ^ 40 * 4657594 * 2
def baseEnd_4657594 : Nat := 2391584415497155375755121

theorem tailTrace_4657594 : CollatzResearch.WordTrace tailWord_4657594 prefixEnd_4657594 2391584415497155375755121 := by
  unfold tailWord_4657594
  simp only [CollatzResearch.WordTrace]
  refine ⟨42469102272084966642750959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113250939392226577714002557 42469102272084966642750959)
  ·
    refine ⟨63703653408127449964126439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42469102272084966642750959 63703653408127449964126439)
    ·
      refine ⟨95555480112191174946189659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63703653408127449964126439 95555480112191174946189659)
      ·
        refine ⟨143333220168286762419284489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95555480112191174946189659 143333220168286762419284489)
        ·
          refine ⟨107499915126215071814463367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143333220168286762419284489 107499915126215071814463367)
          ·
            refine ⟨161249872689322607721695051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107499915126215071814463367 161249872689322607721695051)
            ·
              refine ⟨241874809033983911582542577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161249872689322607721695051 241874809033983911582542577)
              ·
                refine ⟨181406106775487933686906933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241874809033983911582542577 181406106775487933686906933)
                ·
                  refine ⟨17006822510201993783147525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181406106775487933686906933 17006822510201993783147525)
                  ·
                    refine ⟨3188779220662873834340161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17006822510201993783147525 3188779220662873834340161)
                    ·
                      refine ⟨2391584415497155375755121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188779220662873834340161 2391584415497155375755121)
                      ·
                        rfl

theorem cell23_4657594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_4657594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657594 prefixEnd_4657594 := by exact prefixLift 4657594
  have htrace : WordTrace (prefixWord ++ tailWord_4657594) baseStart_4657594 baseEnd_4657594 := by
    simpa [prefixWord, tailWord_4657594, baseEnd_4657594] using wordTrace_append hprefix tailTrace_4657594
  have hstable : (prefixWord ++ tailWord_4657594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657594).length < 2 ^ (prefixWord ++ tailWord_4657594).sum := by decide
  have hdescent : baseEnd_4657594 < baseStart_4657594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657598 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_4657598 : Nat := 118140960795 + 4657598 * 2 ^ 59
def prefixEnd_4657598 : Nat := 4983230072969 + 3 ^ 40 * 4657598 * 2
def baseEnd_4657598 : Nat := 2391586469419773360105103

theorem tailTrace_4657598 : CollatzResearch.WordTrace tailWord_4657598 prefixEnd_4657598 2391586469419773360105103 := by
  unfold tailWord_4657598
  simp only [CollatzResearch.WordTrace]
  refine ⟨21234569372540671906768681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113251036653550250169432965 21234569372540671906768681)
  ·
    refine ⟨15925927029405503930076511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21234569372540671906768681 15925927029405503930076511)
    ·
      refine ⟨23888890544108255895114767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15925927029405503930076511 23888890544108255895114767)
      ·
        refine ⟨35833335816162383842672151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23888890544108255895114767 35833335816162383842672151)
        ·
          refine ⟨53750003724243575764008227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35833335816162383842672151 53750003724243575764008227)
          ·
            refine ⟨80625005586365363646012341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53750003724243575764008227 80625005586365363646012341)
            ·
              refine ⟨7558594273721752841813657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80625005586365363646012341 7558594273721752841813657)
              ·
                refine ⟨5668945705291314631360243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7558594273721752841813657 5668945705291314631360243)
                ·
                  refine ⟨8503418557936971947040365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5668945705291314631360243 8503418557936971947040365)
                  ·
                    refine ⟨3188781959226364480140137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8503418557936971947040365 3188781959226364480140137)
                    ·
                      refine ⟨2391586469419773360105103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188781959226364480140137 2391586469419773360105103)
                      ·
                        rfl

theorem cell23_4657598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_4657598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657598 prefixEnd_4657598 := by exact prefixLift 4657598
  have htrace : WordTrace (prefixWord ++ tailWord_4657598) baseStart_4657598 baseEnd_4657598 := by
    simpa [prefixWord, tailWord_4657598, baseEnd_4657598] using wordTrace_append hprefix tailTrace_4657598
  have hstable : (prefixWord ++ tailWord_4657598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657598).length < 2 ^ (prefixWord ++ tailWord_4657598).sum := by decide
  have hdescent : baseEnd_4657598 < baseStart_4657598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657644 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_4657644 : Nat := 118140960795 + 4657644 * 2 ^ 59
def prefixEnd_4657644 : Nat := 4983230072969 + 3 ^ 40 * 4657644 * 2
def baseEnd_4657644 : Nat := 2391610089529880180129891

theorem tailTrace_4657644 : CollatzResearch.WordTrace tailWord_4657644 prefixEnd_4657644 2391610089529880180129891 := by
  unfold tailWord_4657644
  simp only [CollatzResearch.WordTrace]
  refine ⟨84939116369079362555161993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113252155158772483406882657 84939116369079362555161993)
  ·
    refine ⟨63704337276809521916371495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84939116369079362555161993 63704337276809521916371495)
    ·
      refine ⟨95556505915214282874557243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63704337276809521916371495 95556505915214282874557243)
      ·
        refine ⟨143334758872821424311835865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95556505915214282874557243 143334758872821424311835865)
        ·
          refine ⟨107501069154616068233876899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143334758872821424311835865 107501069154616068233876899)
          ·
            refine ⟨161251603731924102350815349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107501069154616068233876899 161251603731924102350815349)
            ·
              refine ⟨15117337849867884595388939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161251603731924102350815349 15117337849867884595388939)
              ·
                refine ⟨22676006774801826893083409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15117337849867884595388939 22676006774801826893083409)
                ·
                  refine ⟨17007005081101370169812557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22676006774801826893083409 17007005081101370169812557)
                  ·
                    refine ⟨6377626905413013813679709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17007005081101370169812557 6377626905413013813679709)
                    ·
                      refine ⟨2391610089529880180129891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6377626905413013813679709 2391610089529880180129891)
                      ·
                        rfl

theorem cell23_4657644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_4657644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657644 prefixEnd_4657644 := by exact prefixLift 4657644
  have htrace : WordTrace (prefixWord ++ tailWord_4657644) baseStart_4657644 baseEnd_4657644 := by
    simpa [prefixWord, tailWord_4657644, baseEnd_4657644] using wordTrace_append hprefix tailTrace_4657644
  have hstable : (prefixWord ++ tailWord_4657644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657644).length < 2 ^ (prefixWord ++ tailWord_4657644).sum := by decide
  have hdescent : baseEnd_4657644 < baseStart_4657644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657645 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4657645 : Nat := 118140960795 + 4657645 * 2 ^ 59
def prefixEnd_4657645 : Nat := 4983230072969 + 3 ^ 40 * 4657645 * 2
def baseEnd_4657645 : Nat := 2391610603010534676217387

theorem tailTrace_4657645 : CollatzResearch.WordTrace tailWord_4657645 prefixEnd_4657645 2391610603010534676217387 := by
  unfold tailWord_4657645
  simp only [CollatzResearch.WordTrace]
  refine ⟨169878269211155102281110389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113252179474103401520740259 169878269211155102281110389)
  ·
    refine ⟨15926087738545790838854099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169878269211155102281110389 15926087738545790838854099)
    ·
      refine ⟨23889131607818686258281149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15926087738545790838854099 23889131607818686258281149)
      ·
        refine ⟨8958424352932007346855431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23889131607818686258281149 8958424352932007346855431)
        ·
          refine ⟨13437636529398011020283147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8958424352932007346855431 13437636529398011020283147)
          ·
            refine ⟨20156454794097016530424721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13437636529398011020283147 20156454794097016530424721)
            ·
              refine ⟨15117341095572762397818541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20156454794097016530424721 15117341095572762397818541)
              ·
                refine ⟨5669002910839785899181953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15117341095572762397818541 5669002910839785899181953)
                ·
                  refine ⟨4251752183129839424386465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5669002910839785899181953 4251752183129839424386465)
                  ·
                    refine ⟨3188814137347379568289849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4251752183129839424386465 3188814137347379568289849)
                    ·
                      refine ⟨2391610603010534676217387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188814137347379568289849 2391610603010534676217387)
                      ·
                        rfl

theorem cell23_4657645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4657645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657645 prefixEnd_4657645 := by exact prefixLift 4657645
  have htrace : WordTrace (prefixWord ++ tailWord_4657645) baseStart_4657645 baseEnd_4657645 := by
    simpa [prefixWord, tailWord_4657645, baseEnd_4657645] using wordTrace_append hprefix tailTrace_4657645
  have hstable : (prefixWord ++ tailWord_4657645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657645).length < 2 ^ (prefixWord ++ tailWord_4657645).sum := by decide
  have hdescent : baseEnd_4657645 < baseStart_4657645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657647 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 1, 7]
def baseStart_4657647 : Nat := 118140960795 + 4657647 * 2 ^ 59
def prefixEnd_4657647 : Nat := 4983230072969 + 3 ^ 40 * 4657647 * 2
def baseEnd_4657647 : Nat := 797203876657281222797459

theorem tailTrace_4657647 : CollatzResearch.WordTrace tailWord_4657647 prefixEnd_4657647 797203876657281222797459 := by
  unfold tailWord_4657647
  simp only [CollatzResearch.WordTrace]
  refine ⟨169878342157147856622683195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113252228104765237748455463 169878342157147856622683195)
  ·
    refine ⟨254817513235721784934024793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169878342157147856622683195 254817513235721784934024793)
    ·
      refine ⟨191113134926791338700518595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254817513235721784934024793 191113134926791338700518595)
      ·
        refine ⟨286669702390187008050777893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191113134926791338700518595 286669702390187008050777893)
        ·
          refine ⟨53750569198160064009520855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286669702390187008050777893 53750569198160064009520855)
          ·
            refine ⟨80625853797240096014281283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53750569198160064009520855 80625853797240096014281283)
            ·
              refine ⟨120938780695860144021421925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80625853797240096014281283 120938780695860144021421925)
              ·
                refine ⟨22676021380473777004016611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120938780695860144021421925 22676021380473777004016611)
                ·
                  refine ⟨34014032070710665506024917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22676021380473777004016611 34014032070710665506024917)
                  ·
                    refine ⟨797203876657281222797459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34014032070710665506024917 797203876657281222797459)
                    ·
                      rfl

theorem cell23_4657647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_4657647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657647 prefixEnd_4657647 := by exact prefixLift 4657647
  have htrace : WordTrace (prefixWord ++ tailWord_4657647) baseStart_4657647 baseEnd_4657647 := by
    simpa [prefixWord, tailWord_4657647, baseEnd_4657647] using wordTrace_append hprefix tailTrace_4657647
  have hstable : (prefixWord ++ tailWord_4657647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657647).length < 2 ^ (prefixWord ++ tailWord_4657647).sum := by decide
  have hdescent : baseEnd_4657647 < baseStart_4657647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657657 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_4657657 : Nat := 118140960795 + 4657657 * 2 ^ 59
def prefixEnd_4657657 : Nat := 4983230072969 + 3 ^ 40 * 4657657 * 2
def baseEnd_4657657 : Nat := 2391616764778388629267331

theorem tailTrace_4657657 : CollatzResearch.WordTrace tailWord_4657657 prefixEnd_4657657 2391616764778388629267331 := by
  unfold tailWord_4657657
  simp only [CollatzResearch.WordTrace]
  refine ⟨169878706887111628330547225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113252471258074418887031483 169878706887111628330547225)
  ·
    refine ⟨127409030165333721247910419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169878706887111628330547225 127409030165333721247910419)
    ·
      refine ⟨191113545248000581871865629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127409030165333721247910419 191113545248000581871865629)
      ·
        refine ⟨71667579468000218201949611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191113545248000581871865629 71667579468000218201949611)
        ·
          refine ⟨107501369202000327302924417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71667579468000218201949611 107501369202000327302924417)
          ·
            refine ⟨80626026901500245477193313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107501369202000327302924417 80626026901500245477193313)
            ·
              refine ⟨60469520176125184107894985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80626026901500245477193313 60469520176125184107894985)
              ·
                refine ⟨45352140132093888080921239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60469520176125184107894985 45352140132093888080921239)
                ·
                  refine ⟨68028210198140832121381859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45352140132093888080921239 68028210198140832121381859)
                  ·
                    refine ⟨102042315297211248182072789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68028210198140832121381859 102042315297211248182072789)
                    ·
                      refine ⟨2391616764778388629267331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102042315297211248182072789 2391616764778388629267331)
                      ·
                        rfl

theorem cell23_4657657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_4657657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657657 prefixEnd_4657657 := by exact prefixLift 4657657
  have htrace : WordTrace (prefixWord ++ tailWord_4657657) baseStart_4657657 baseEnd_4657657 := by
    simpa [prefixWord, tailWord_4657657, baseEnd_4657657] using wordTrace_append hprefix tailTrace_4657657
  have hstable : (prefixWord ++ tailWord_4657657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657657).length < 2 ^ (prefixWord ++ tailWord_4657657).sum := by decide
  have hdescent : baseEnd_4657657 < baseStart_4657657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657668 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 5]
def baseStart_4657668 : Nat := 118140960795 + 4657668 * 2 ^ 59
def prefixEnd_4657668 : Nat := 4983230072969 + 3 ^ 40 * 4657668 * 2
def baseEnd_4657668 : Nat := 265735823673954231803309

theorem tailTrace_4657668 : CollatzResearch.WordTrace tailWord_4657668 prefixEnd_4657668 265735823673954231803309 := by
  unfold tailWord_4657668
  simp only [CollatzResearch.WordTrace]
  refine ⟨84939554045035888604598829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113252738726714518139465105 84939554045035888604598829)
  ·
    refine ⟨31852332766888458226724561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84939554045035888604598829 31852332766888458226724561)
    ·
      refine ⟨23889249575166343670043421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31852332766888458226724561 23889249575166343670043421)
      ·
        refine ⟨8958468590687378876266283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23889249575166343670043421 8958468590687378876266283)
        ·
          refine ⟨13437702886031068314399425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8958468590687378876266283 13437702886031068314399425)
          ·
            refine ⟨10078277164523301235799569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13437702886031068314399425 10078277164523301235799569)
            ·
              refine ⟨7558707873392475926849677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10078277164523301235799569 7558707873392475926849677)
              ·
                refine ⟨2834515452522178472568629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7558707873392475926849677 2834515452522178472568629)
                ·
                  refine ⟨265735823673954231803309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2834515452522178472568629 265735823673954231803309)
                  ·
                    rfl

theorem cell23_4657668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_4657668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657668 prefixEnd_4657668 := by exact prefixLift 4657668
  have htrace : WordTrace (prefixWord ++ tailWord_4657668) baseStart_4657668 baseEnd_4657668 := by
    simpa [prefixWord, tailWord_4657668, baseEnd_4657668] using wordTrace_append hprefix tailTrace_4657668
  have hstable : (prefixWord ++ tailWord_4657668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657668).length < 2 ^ (prefixWord ++ tailWord_4657668).sum := by decide
  have hdescent : baseEnd_4657668 < baseStart_4657668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657701 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 2, 4, 2]
def baseStart_4657701 : Nat := 118140960795 + 4657701 * 2 ^ 59
def prefixEnd_4657701 : Nat := 4983230072969 + 3 ^ 40 * 4657701 * 2
def baseEnd_4657701 : Nat := 2391639357927186457117129

theorem tailTrace_4657701 : CollatzResearch.WordTrace tailWord_4657701 prefixEnd_4657701 2391639357927186457117129 := by
  unfold tailWord_4657701
  simp only [CollatzResearch.WordTrace]
  refine ⟨169880311698952223845148957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113253541132634815896765971 169880311698952223845148957)
  ·
    refine ⟨63705116887107083941930859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169880311698952223845148957 63705116887107083941930859)
    ·
      refine ⟨95557675330660625912896289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63705116887107083941930859 95557675330660625912896289)
      ·
        refine ⟨71668256497995469434672217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95557675330660625912896289 71668256497995469434672217)
        ·
          refine ⟨53751192373496602076004163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71668256497995469434672217 53751192373496602076004163)
          ·
            refine ⟨80626788560244903114006245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53751192373496602076004163 80626788560244903114006245)
            ·
              refine ⟨15117522855045919333876171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80626788560244903114006245 15117522855045919333876171)
              ·
                refine ⟨22676284282568879000814257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15117522855045919333876171 22676284282568879000814257)
                ·
                  refine ⟨17007213211926659250610693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22676284282568879000814257 17007213211926659250610693)
                  ·
                    refine ⟨3188852477236248609489505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17007213211926659250610693 3188852477236248609489505)
                    ·
                      refine ⟨2391639357927186457117129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188852477236248609489505 2391639357927186457117129)
                      ·
                        rfl

theorem cell23_4657701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_4657701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657701 prefixEnd_4657701 := by exact prefixLift 4657701
  have htrace : WordTrace (prefixWord ++ tailWord_4657701) baseStart_4657701 baseEnd_4657701 := by
    simpa [prefixWord, tailWord_4657701, baseEnd_4657701] using wordTrace_append hprefix tailTrace_4657701
  have hstable : (prefixWord ++ tailWord_4657701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657701).length < 2 ^ (prefixWord ++ tailWord_4657701).sum := by decide
  have hdescent : baseEnd_4657701 < baseStart_4657701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657721 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4657721 : Nat := 118140960795 + 4657721 * 2 ^ 59
def prefixEnd_4657721 : Nat := 4983230072969 + 3 ^ 40 * 4657721 * 2
def baseEnd_4657721 : Nat := 2391649627540276378867037

theorem tailTrace_4657721 : CollatzResearch.WordTrace tailWord_4657721 prefixEnd_4657721 2391649627540276378867037 := by
  unfold tailWord_4657721
  simp only [CollatzResearch.WordTrace]
  refine ⟨169881041158879767260877017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113254027439253178173918011 169881041158879767260877017)
  ·
    refine ⟨127410780869159825445657763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169881041158879767260877017 127410780869159825445657763)
    ·
      refine ⟨191116171303739738168486645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127410780869159825445657763 191116171303739738168486645)
      ·
        refine ⟨17917141059725600453295623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191116171303739738168486645 17917141059725600453295623)
        ·
          refine ⟨26875711589588400679943435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17917141059725600453295623 26875711589588400679943435)
          ·
            refine ⟨40313567384382601019915153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26875711589588400679943435 40313567384382601019915153)
            ·
              refine ⟨30235175538286950764936365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40313567384382601019915153 30235175538286950764936365)
              ·
                refine ⟨11338190826857606536851137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30235175538286950764936365 11338190826857606536851137)
                ·
                  refine ⟨8503643120143204902638353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11338190826857606536851137 8503643120143204902638353)
                  ·
                    refine ⟨6377732340107403676978765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8503643120143204902638353 6377732340107403676978765)
                    ·
                      refine ⟨2391649627540276378867037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6377732340107403676978765 2391649627540276378867037)
                      ·
                        rfl

theorem cell23_4657721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4657721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657721 prefixEnd_4657721 := by exact prefixLift 4657721
  have htrace : WordTrace (prefixWord ++ tailWord_4657721) baseStart_4657721 baseEnd_4657721 := by
    simpa [prefixWord, tailWord_4657721, baseEnd_4657721] using wordTrace_append hprefix tailTrace_4657721
  have hstable : (prefixWord ++ tailWord_4657721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657721).length < 2 ^ (prefixWord ++ tailWord_4657721).sum := by decide
  have hdescent : baseEnd_4657721 < baseStart_4657721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657724 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 8]
def baseStart_4657724 : Nat := 118140960795 + 4657724 * 2 ^ 59
def prefixEnd_4657724 : Nat := 4983230072969 + 3 ^ 40 * 4657724 * 2
def baseEnd_4657724 : Nat := 265739018664693318569947

theorem tailTrace_4657724 : CollatzResearch.WordTrace tailWord_4657724 prefixEnd_4657724 265739018664693318569947 := by
  unfold tailWord_4657724
  simp only [CollatzResearch.WordTrace]
  refine ⟨84940575288934449386618113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113254100385245932515490817 84940575288934449386618113)
  ·
    refine ⟨63705431466700837039963585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84940575288934449386618113 63705431466700837039963585)
    ·
      refine ⟨47779073600025627779972689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63705431466700837039963585 47779073600025627779972689)
      ·
        refine ⟨35834305200019220834979517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47779073600025627779972689 35834305200019220834979517)
        ·
          refine ⟨13437864450007207813117319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35834305200019220834979517 13437864450007207813117319)
          ·
            refine ⟨20156796675010811719675979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13437864450007207813117319 20156796675010811719675979)
            ·
              refine ⟨30235195012516217579513969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20156796675010811719675979 30235195012516217579513969)
              ·
                refine ⟨22676396259387163184635477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30235195012516217579513969 22676396259387163184635477)
                ·
                  refine ⟨265739018664693318569947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22676396259387163184635477 265739018664693318569947)
                  ·
                    rfl

theorem cell23_4657724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_4657724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657724 prefixEnd_4657724 := by exact prefixLift 4657724
  have htrace : WordTrace (prefixWord ++ tailWord_4657724) baseStart_4657724 baseEnd_4657724 := by
    simpa [prefixWord, tailWord_4657724, baseEnd_4657724] using wordTrace_append hprefix tailTrace_4657724
  have hstable : (prefixWord ++ tailWord_4657724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657724).length < 2 ^ (prefixWord ++ tailWord_4657724).sum := by decide
  have hdescent : baseEnd_4657724 < baseStart_4657724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657728 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 1, 4]
def baseStart_4657728 : Nat := 118140960795 + 4657728 * 2 ^ 59
def prefixEnd_4657728 : Nat := 4983230072969 + 3 ^ 40 * 4657728 * 2
def baseEnd_4657728 : Nat := 797217740634952617159835

theorem tailTrace_4657728 : CollatzResearch.WordTrace tailWord_4657728 prefixEnd_4657728 797217740634952617159835 := by
  unfold tailWord_4657728
  simp only [CollatzResearch.WordTrace]
  refine ⟨84940648234927203728190919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113254197646569604970921225 84940648234927203728190919)
  ·
    refine ⟨127410972352390805592286379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84940648234927203728190919 127410972352390805592286379)
    ·
      refine ⟨191116458528586208388429569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127410972352390805592286379 191116458528586208388429569)
      ·
        refine ⟨143337343896439656291322177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191116458528586208388429569 143337343896439656291322177)
        ·
          refine ⟨107503007922329742218491633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143337343896439656291322177 107503007922329742218491633)
          ·
            refine ⟨80627255941747306663868725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107503007922329742218491633 80627255941747306663868725)
            ·
              refine ⟨7558805244538809999737693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80627255941747306663868725 7558805244538809999737693)
              ·
                refine ⟨2834551966702053749901635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7558805244538809999737693 2834551966702053749901635)
                ·
                  refine ⟨4251827950053080624852453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834551966702053749901635 4251827950053080624852453)
                  ·
                    refine ⟨797217740634952617159835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251827950053080624852453 797217740634952617159835)
                    ·
                      rfl

theorem cell23_4657728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 4].length) (baseStart_4657728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657728 prefixEnd_4657728 := by exact prefixLift 4657728
  have htrace : WordTrace (prefixWord ++ tailWord_4657728) baseStart_4657728 baseEnd_4657728 := by
    simpa [prefixWord, tailWord_4657728, baseEnd_4657728] using wordTrace_append hprefix tailTrace_4657728
  have hstable : (prefixWord ++ tailWord_4657728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657728).length < 2 ^ (prefixWord ++ tailWord_4657728).sum := by decide
  have hdescent : baseEnd_4657728 < baseStart_4657728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657741 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 8]
def baseStart_4657741 : Nat := 118140960795 + 4657741 * 2 ^ 59
def prefixEnd_4657741 : Nat := 4983230072969 + 3 ^ 40 * 4657741 * 2
def baseEnd_4657741 : Nat := 265739988572596255624105

theorem tailTrace_4657741 : CollatzResearch.WordTrace tailWord_4657741 prefixEnd_4657741 265739988572596255624105 := by
  unfold tailWord_4657741
  simp only [CollatzResearch.WordTrace]
  refine ⟨169881770618807310676605077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113254513745871540451070051 169881770618807310676605077)
  ·
    refine ⟨7963207997756592687965863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169881770618807310676605077 7963207997756592687965863)
    ·
      refine ⟨11944811996634889031948795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7963207997756592687965863 11944811996634889031948795)
      ·
        refine ⟨17917217994952333547923193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11944811996634889031948795 17917217994952333547923193)
        ·
          refine ⟨13437913496214250160942395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17917217994952333547923193 13437913496214250160942395)
          ·
            refine ⟨20156870244321375241413593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13437913496214250160942395 20156870244321375241413593)
            ·
              refine ⟨15117652683241031431060195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20156870244321375241413593 15117652683241031431060195)
              ·
                refine ⟨22676479024861547146590293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15117652683241031431060195 22676479024861547146590293)
                ·
                  refine ⟨265739988572596255624105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22676479024861547146590293 265739988572596255624105)
                  ·
                    rfl

theorem cell23_4657741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_4657741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657741 prefixEnd_4657741 := by exact prefixLift 4657741
  have htrace : WordTrace (prefixWord ++ tailWord_4657741) baseStart_4657741 baseEnd_4657741 := by
    simpa [prefixWord, tailWord_4657741, baseEnd_4657741] using wordTrace_append hprefix tailTrace_4657741
  have hstable : (prefixWord ++ tailWord_4657741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657741).length < 2 ^ (prefixWord ++ tailWord_4657741).sum := by decide
  have hdescent : baseEnd_4657741 < baseStart_4657741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657745 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 1, 4]
def baseStart_4657745 : Nat := 118140960795 + 4657745 * 2 ^ 59
def prefixEnd_4657745 : Nat := 4983230072969 + 3 ^ 40 * 4657745 * 2
def baseEnd_4657745 : Nat := 797220650358661428322309

theorem tailTrace_4657745 : CollatzResearch.WordTrace tailWord_4657745 prefixEnd_4657745 797220650358661428322309 := by
  unfold tailWord_4657745
  simp only [CollatzResearch.WordTrace]
  refine ⟨169881916510792819359750689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113254611007195212906500459 169881916510792819359750689)
  ·
    refine ⟨127411437383094614519813017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169881916510792819359750689 127411437383094614519813017)
    ·
      refine ⟨95558578037320960889859763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127411437383094614519813017 95558578037320960889859763)
      ·
        refine ⟨143337867055981441334789645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95558578037320960889859763 143337867055981441334789645)
        ·
          refine ⟨53751700145993040500546117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143337867055981441334789645 53751700145993040500546117)
          ·
            refine ⟨10078443777373695093852397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53751700145993040500546117 10078443777373695093852397)
            ·
              refine ⟨3779416416515135660194649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10078443777373695093852397 3779416416515135660194649)
              ·
                refine ⟨2834562312386351745145987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779416416515135660194649 2834562312386351745145987)
                ·
                  refine ⟨4251843468579527617718981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834562312386351745145987 4251843468579527617718981)
                  ·
                    refine ⟨797220650358661428322309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251843468579527617718981 797220650358661428322309)
                    ·
                      rfl

theorem cell23_4657745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_4657745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657745 prefixEnd_4657745 := by exact prefixLift 4657745
  have htrace : WordTrace (prefixWord ++ tailWord_4657745) baseStart_4657745 baseEnd_4657745 := by
    simpa [prefixWord, tailWord_4657745, baseEnd_4657745] using wordTrace_append hprefix tailTrace_4657745
  have hstable : (prefixWord ++ tailWord_4657745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657745).length < 2 ^ (prefixWord ++ tailWord_4657745).sum := by decide
  have hdescent : baseEnd_4657745 < baseStart_4657745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657784 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_4657784 : Nat := 118140960795 + 4657784 * 2 ^ 59
def prefixEnd_4657784 : Nat := 4983230072969 + 3 ^ 40 * 4657784 * 2
def baseEnd_4657784 : Nat := 797227325607169877459749

theorem tailTrace_4657784 : CollatzResearch.WordTrace tailWord_4657784 prefixEnd_4657784 797227325607169877459749 := by
  unfold tailWord_4657784
  simp only [CollatzResearch.WordTrace]
  refine ⟨84941669478825764510210203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113255559305101019346946937 84941669478825764510210203)
  ·
    refine ⟨127412504218238646765315305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84941669478825764510210203 127412504218238646765315305)
    ·
      refine ⟨95559378163678985073986479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127412504218238646765315305 95559378163678985073986479)
      ·
        refine ⟨143339067245518477610979719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95559378163678985073986479 143339067245518477610979719)
        ·
          refine ⟨215008600868277716416469579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143339067245518477610979719 215008600868277716416469579)
          ·
            refine ⟨322512901302416574624704369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215008600868277716416469579 322512901302416574624704369)
            ·
              refine ⟨241884675976812430968528277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322512901302416574624704369 241884675976812430968528277)
              ·
                refine ⟨11338344186413082701649763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 241884675976812430968528277 11338344186413082701649763)
                ·
                  refine ⟨17007516279619624052474645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11338344186413082701649763 17007516279619624052474645)
                  ·
                    refine ⟨797227325607169877459749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17007516279619624052474645 797227325607169877459749)
                    ·
                      rfl

theorem cell23_4657784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_4657784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657784 prefixEnd_4657784 := by exact prefixLift 4657784
  have htrace : WordTrace (prefixWord ++ tailWord_4657784) baseStart_4657784 baseEnd_4657784 := by
    simpa [prefixWord, tailWord_4657784, baseEnd_4657784] using wordTrace_append hprefix tailTrace_4657784
  have hstable : (prefixWord ++ tailWord_4657784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657784).length < 2 ^ (prefixWord ++ tailWord_4657784).sum := by decide
  have hdescent : baseEnd_4657784 < baseStart_4657784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657802 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_4657802 : Nat := 118140960795 + 4657802 * 2 ^ 59
def prefixEnd_4657802 : Nat := 4983230072969 + 3 ^ 40 * 4657802 * 2
def baseEnd_4657802 : Nat := 2391691219473290561954165

theorem tailTrace_4657802 : CollatzResearch.WordTrace tailWord_4657802 prefixEnd_4657802 2391691219473290561954165 := by
  unfold tailWord_4657802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42470998867896579523643915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113255996981057545396383773 42470998867896579523643915)
  ·
    refine ⟨63706498301844869285465873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42470998867896579523643915 63706498301844869285465873)
    ·
      refine ⟨47779873726383651964099405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63706498301844869285465873 47779873726383651964099405)
      ·
        refine ⟨17917452647393869486537277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47779873726383651964099405 17917452647393869486537277)
        ·
          refine ⟨6719044742772701057451479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17917452647393869486537277 6719044742772701057451479)
          ·
            refine ⟨10078567114159051586177219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719044742772701057451479 10078567114159051586177219)
            ·
              refine ⟨15117850671238577379265829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078567114159051586177219 15117850671238577379265829)
              ·
                refine ⟨2834597000857233258612343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15117850671238577379265829 2834597000857233258612343)
                ·
                  refine ⟨4251895501285849887918515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834597000857233258612343 4251895501285849887918515)
                  ·
                    refine ⟨6377843251928774831877773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4251895501285849887918515 6377843251928774831877773)
                    ·
                      refine ⟨2391691219473290561954165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6377843251928774831877773 2391691219473290561954165)
                      ·
                        rfl

theorem cell23_4657802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_4657802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657802 prefixEnd_4657802 := by exact prefixLift 4657802
  have htrace : WordTrace (prefixWord ++ tailWord_4657802) baseStart_4657802 baseEnd_4657802 := by
    simpa [prefixWord, tailWord_4657802, baseEnd_4657802] using wordTrace_append hprefix tailTrace_4657802
  have hstable : (prefixWord ++ tailWord_4657802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657802).length < 2 ^ (prefixWord ++ tailWord_4657802).sum := by decide
  have hdescent : baseEnd_4657802 < baseStart_4657802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657804 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_4657804 : Nat := 118140960795 + 4657804 * 2 ^ 59
def prefixEnd_4657804 : Nat := 4983230072969 + 3 ^ 40 * 4657804 * 2
def baseEnd_4657804 : Nat := 2391692246434599554129155

theorem tailTrace_4657804 : CollatzResearch.WordTrace tailWord_4657804 prefixEnd_4657804 2391692246434599554129155 := by
  unfold tailWord_4657804
  simp only [CollatzResearch.WordTrace]
  refine ⟨84942034208789536218074233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113256045611719381624098977 84942034208789536218074233)
  ·
    refine ⟨63706525656592152163555675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84942034208789536218074233 63706525656592152163555675)
    ·
      refine ⟨95559788484888228245333513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63706525656592152163555675 95559788484888228245333513)
      ·
        refine ⟨71669841363666171184000135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95559788484888228245333513 71669841363666171184000135)
        ·
          refine ⟨107504762045499256776000203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71669841363666171184000135 107504762045499256776000203)
          ·
            refine ⟨161257143068248885164000305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107504762045499256776000203 161257143068248885164000305)
            ·
              refine ⟨120942857301186663873000229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161257143068248885164000305 120942857301186663873000229)
              ·
                refine ⟨22676785743972499476187543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120942857301186663873000229 22676785743972499476187543)
                ·
                  refine ⟨34015178615958749214281315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22676785743972499476187543 34015178615958749214281315)
                  ·
                    refine ⟨51022767923938123821421973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34015178615958749214281315 51022767923938123821421973)
                    ·
                      refine ⟨2391692246434599554129155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51022767923938123821421973 2391692246434599554129155)
                      ·
                        rfl

theorem cell23_4657804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_4657804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657804 prefixEnd_4657804 := by exact prefixLift 4657804
  have htrace : WordTrace (prefixWord ++ tailWord_4657804) baseStart_4657804 baseEnd_4657804 := by
    simpa [prefixWord, tailWord_4657804, baseEnd_4657804] using wordTrace_append hprefix tailTrace_4657804
  have hstable : (prefixWord ++ tailWord_4657804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657804).length < 2 ^ (prefixWord ++ tailWord_4657804).sum := by decide
  have hdescent : baseEnd_4657804 < baseStart_4657804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657821 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4657821 : Nat := 118140960795 + 4657821 * 2 ^ 59
def prefixEnd_4657821 : Nat := 4983230072969 + 3 ^ 40 * 4657821 * 2
def baseEnd_4657821 : Nat := 2391700975605725987616577

theorem tailTrace_4657821 : CollatzResearch.WordTrace tailWord_4657821 prefixEnd_4657821 2391700975605725987616577 := by
  unfold tailWord_4657821
  simp only [CollatzResearch.WordTrace]
  refine ⟨169884688458517484339517317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113256458972344989559678211 169884688458517484339517317)
  ·
    refine ⟨31853379085972028313659497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169884688458517484339517317 31853379085972028313659497)
    ·
      refine ⟨23890034314479021235244623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31853379085972028313659497 23890034314479021235244623)
      ·
        refine ⟨35835051471718531852866935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23890034314479021235244623 35835051471718531852866935)
        ·
          refine ⟨53752577207577797779300403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35835051471718531852866935 53752577207577797779300403)
          ·
            refine ⟨80628865811366696668950605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53752577207577797779300403 80628865811366696668950605)
            ·
              refine ⟨30235824679262511250856477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80628865811366696668950605 30235824679262511250856477)
              ·
                refine ⟨11338434254723441719071179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30235824679262511250856477 11338434254723441719071179)
                ·
                  refine ⟨17007651382085162578606769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11338434254723441719071179 17007651382085162578606769)
                  ·
                    refine ⟨12755738536563871933955077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17007651382085162578606769 12755738536563871933955077)
                    ·
                      refine ⟨2391700975605725987616577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12755738536563871933955077 2391700975605725987616577)
                      ·
                        rfl

theorem cell23_4657821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4657821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657821 prefixEnd_4657821 := by exact prefixLift 4657821
  have htrace : WordTrace (prefixWord ++ tailWord_4657821) baseStart_4657821 baseEnd_4657821 := by
    simpa [prefixWord, tailWord_4657821, baseEnd_4657821] using wordTrace_append hprefix tailTrace_4657821
  have hstable : (prefixWord ++ tailWord_4657821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657821).length < 2 ^ (prefixWord ++ tailWord_4657821).sum := by decide
  have hdescent : baseEnd_4657821 < baseStart_4657821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657828 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_4657828 : Nat := 118140960795 + 4657828 * 2 ^ 59
def prefixEnd_4657828 : Nat := 4983230072969 + 3 ^ 40 * 4657828 * 2
def baseEnd_4657828 : Nat := 2391704569970307460229045

theorem tailTrace_4657828 : CollatzResearch.WordTrace tailWord_4657828 prefixEnd_4657828 2391704569970307460229045 := by
  unfold tailWord_4657828
  simp only [CollatzResearch.WordTrace]
  refine ⟨84942471884746062267511069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113256629179661416356681425 84942471884746062267511069)
  ·
    refine ⟨31853426956779773350316651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84942471884746062267511069 31853426956779773350316651)
    ·
      refine ⟨47780140435169660025474977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31853426956779773350316651 47780140435169660025474977)
      ·
        refine ⟨35835105326377245019106233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47780140435169660025474977 35835105326377245019106233)
        ·
          refine ⟨26876328994782933764329675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35835105326377245019106233 26876328994782933764329675)
          ·
            refine ⟨40314493492174400646494513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26876328994782933764329675 40314493492174400646494513)
            ·
              refine ⟨30235870119130800484870885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40314493492174400646494513 30235870119130800484870885)
              ·
                refine ⟨5669225647337025090913291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30235870119130800484870885 5669225647337025090913291)
                ·
                  refine ⟨8503838471005537636369937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669225647337025090913291 8503838471005537636369937)
                  ·
                    refine ⟨6377878853254153227277453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8503838471005537636369937 6377878853254153227277453)
                    ·
                      refine ⟨2391704569970307460229045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6377878853254153227277453 2391704569970307460229045)
                      ·
                        rfl

theorem cell23_4657828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_4657828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657828 prefixEnd_4657828 := by exact prefixLift 4657828
  have htrace : WordTrace (prefixWord ++ tailWord_4657828) baseStart_4657828 baseEnd_4657828 := by
    simpa [prefixWord, tailWord_4657828, baseEnd_4657828] using wordTrace_append hprefix tailTrace_4657828
  have hstable : (prefixWord ++ tailWord_4657828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657828).length < 2 ^ (prefixWord ++ tailWord_4657828).sum := by decide
  have hdescent : baseEnd_4657828 < baseStart_4657828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657845 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4657845 : Nat := 118140960795 + 4657845 * 2 ^ 59
def prefixEnd_4657845 : Nat := 4983230072969 + 3 ^ 40 * 4657845 * 2
def baseEnd_4657845 : Nat := 2391713299141433893716467

theorem tailTrace_4657845 : CollatzResearch.WordTrace tailWord_4657845 prefixEnd_4657845 2391713299141433893716467 := by
  unfold tailWord_4657845
  simp only [CollatzResearch.WordTrace]
  refine ⟨169885563810430536438390989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113257042540287024292260659 169885563810430536438390989)
  ·
    refine ⟨63707086428911451164396621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169885563810430536438390989 63707086428911451164396621)
    ·
      refine ⟨23890157410841794186648733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63707086428911451164396621 23890157410841794186648733)
      ·
        refine ⟨8958809029065672819993275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23890157410841794186648733 8958809029065672819993275)
        ·
          refine ⟨13438213543598509229989913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8958809029065672819993275 13438213543598509229989913)
          ·
            refine ⟨10078660157698881922492435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13438213543598509229989913 10078660157698881922492435)
            ·
              refine ⟨15117990236548322883738653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078660157698881922492435 15117990236548322883738653)
              ·
                refine ⟨5669246338705621081401995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15117990236548322883738653 5669246338705621081401995)
                ·
                  refine ⟨8503869508058431622102993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669246338705621081401995 8503869508058431622102993)
                  ·
                    refine ⟨6377902131043823716577245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8503869508058431622102993 6377902131043823716577245)
                    ·
                      refine ⟨2391713299141433893716467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6377902131043823716577245 2391713299141433893716467)
                      ·
                        rfl

theorem cell23_4657845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4657845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657845 prefixEnd_4657845 := by exact prefixLift 4657845
  have htrace : WordTrace (prefixWord ++ tailWord_4657845) baseStart_4657845 baseEnd_4657845 := by
    simpa [prefixWord, tailWord_4657845, baseEnd_4657845] using wordTrace_append hprefix tailTrace_4657845
  have hstable : (prefixWord ++ tailWord_4657845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657845).length < 2 ^ (prefixWord ++ tailWord_4657845).sum := by decide
  have hdescent : baseEnd_4657845 < baseStart_4657845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657862 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4657862 : Nat := 118140960795 + 4657862 * 2 ^ 59
def prefixEnd_4657862 : Nat := 4983230072969 + 3 ^ 40 * 4657862 * 2
def baseEnd_4657862 : Nat := 2391722028312560327203889

theorem tailTrace_4657862 : CollatzResearch.WordTrace tailWord_4657862 prefixEnd_4657862 2391722028312560327203889 := by
  unfold tailWord_4657862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308943245355279635679995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113257455900912632227839893 5308943245355279635679995)
  ·
    refine ⟨7963414868032919453519993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5308943245355279635679995 7963414868032919453519993)
    ·
      refine ⟨5972561151024689590139995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7963414868032919453519993 5972561151024689590139995)
      ·
        refine ⟨8958841726537034385209993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5972561151024689590139995 8958841726537034385209993)
        ·
          refine ⟨6719131294902775788907495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8958841726537034385209993 6719131294902775788907495)
          ·
            refine ⟨10078696942354163683361243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719131294902775788907495 10078696942354163683361243)
            ·
              refine ⟨15118045413531245525041865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078696942354163683361243 15118045413531245525041865)
              ·
                refine ⟨11338534060148434143781399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15118045413531245525041865 11338534060148434143781399)
                ·
                  refine ⟨17007801090222651215672099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11338534060148434143781399 17007801090222651215672099)
                  ·
                    refine ⟨25511701635333976823508149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17007801090222651215672099 25511701635333976823508149)
                    ·
                      refine ⟨2391722028312560327203889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25511701635333976823508149 2391722028312560327203889)
                      ·
                        rfl

theorem cell23_4657862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4657862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657862 prefixEnd_4657862 := by exact prefixLift 4657862
  have htrace : WordTrace (prefixWord ++ tailWord_4657862) baseStart_4657862 baseEnd_4657862 := by
    simpa [prefixWord, tailWord_4657862, baseEnd_4657862] using wordTrace_append hprefix tailTrace_4657862
  have hstable : (prefixWord ++ tailWord_4657862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657862).length < 2 ^ (prefixWord ++ tailWord_4657862).sum := by decide
  have hdescent : baseEnd_4657862 < baseStart_4657862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657869 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4657869 : Nat := 118140960795 + 4657869 * 2 ^ 59
def prefixEnd_4657869 : Nat := 4983230072969 + 3 ^ 40 * 4657869 * 2
def baseEnd_4657869 : Nat := 797241874225713933272119

theorem tailTrace_4657869 : CollatzResearch.WordTrace tailWord_4657869 prefixEnd_4657869 797241874225713933272119 := by
  unfold tailWord_4657869
  simp only [CollatzResearch.WordTrace]
  refine ⟨169886439162343588537264661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113257626108229059024843107 169886439162343588537264661)
  ·
    refine ⟨7963426835734855712684281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169886439162343588537264661 7963426835734855712684281)
    ·
      refine ⟨5972570126801141784513211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7963426835734855712684281 5972570126801141784513211)
      ·
        refine ⟨8958855190201712676769817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5972570126801141784513211 8958855190201712676769817)
        ·
          refine ⟨6719141392651284507577363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8958855190201712676769817 6719141392651284507577363)
          ·
            refine ⟨10078712088976926761366045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719141392651284507577363 10078712088976926761366045)
            ·
              refine ⟨3779517033366347535512267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10078712088976926761366045 3779517033366347535512267)
              ·
                refine ⟨5669275550049521303268401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779517033366347535512267 5669275550049521303268401)
                ·
                  refine ⟨4251956662537140977451301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5669275550049521303268401 4251956662537140977451301)
                  ·
                    refine ⟨797241874225713933272119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251956662537140977451301 797241874225713933272119)
                    ·
                      rfl

theorem cell23_4657869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4657869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657869 prefixEnd_4657869 := by exact prefixLift 4657869
  have htrace : WordTrace (prefixWord ++ tailWord_4657869) baseStart_4657869 baseEnd_4657869 := by
    simpa [prefixWord, tailWord_4657869, baseEnd_4657869] using wordTrace_append hprefix tailTrace_4657869
  have hstable : (prefixWord ++ tailWord_4657869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657869).length < 2 ^ (prefixWord ++ tailWord_4657869).sum := by decide
  have hdescent : baseEnd_4657869 < baseStart_4657869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657898 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_4657898 : Nat := 118140960795 + 4657898 * 2 ^ 59
def prefixEnd_4657898 : Nat := 4983230072969 + 3 ^ 40 * 4657898 * 2
def baseEnd_4657898 : Nat := 2391740513616122186353723

theorem tailTrace_4657898 : CollatzResearch.WordTrace tailWord_4657898 prefixEnd_4657898 2391740513616122186353723 := by
  unfold tailWord_4657898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42471874219809631622517587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113258331252825684326713565 42471874219809631622517587)
  ·
    refine ⟨63707811329714447433776381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42471874219809631622517587 63707811329714447433776381)
    ·
      refine ⟨23890429248642917787666143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63707811329714447433776381 23890429248642917787666143)
      ·
        refine ⟨35835643872964376681499215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23890429248642917787666143 35835643872964376681499215)
        ·
          refine ⟨53753465809446565022248823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35835643872964376681499215 53753465809446565022248823)
          ·
            refine ⟨80630198714169847533373235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53753465809446565022248823 80630198714169847533373235)
            ·
              refine ⟨120945298071254771300059853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80630198714169847533373235 120945298071254771300059853)
              ·
                refine ⟨45354486776720539237522445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120945298071254771300059853 45354486776720539237522445)
                ·
                  refine ⟨17007932541270202214070917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45354486776720539237522445 17007932541270202214070917)
                  ·
                    refine ⟨3188987351488162915138297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17007932541270202214070917 3188987351488162915138297)
                    ·
                      refine ⟨2391740513616122186353723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3188987351488162915138297 2391740513616122186353723)
                      ·
                        rfl

theorem cell23_4657898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_4657898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657898 prefixEnd_4657898 := by exact prefixLift 4657898
  have htrace : WordTrace (prefixWord ++ tailWord_4657898) baseStart_4657898 baseEnd_4657898 := by
    simpa [prefixWord, tailWord_4657898, baseEnd_4657898] using wordTrace_append hprefix tailTrace_4657898
  have hstable : (prefixWord ++ tailWord_4657898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657898).length < 2 ^ (prefixWord ++ tailWord_4657898).sum := by decide
  have hdescent : baseEnd_4657898 < baseStart_4657898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657931 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 3]
def baseStart_4657931 : Nat := 118140960795 + 4657931 * 2 ^ 59
def prefixEnd_4657931 : Nat := 4983230072969 + 3 ^ 40 * 4657931 * 2
def baseEnd_4657931 : Nat := 2391757458477720557241071

theorem tailTrace_4657931 : CollatzResearch.WordTrace tailWord_4657931 prefixEnd_4657931 2391757458477720557241071 := by
  unfold tailWord_4657931
  simp only [CollatzResearch.WordTrace]
  refine ⟨169888700488118973126021647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113259133658745982084014431 169888700488118973126021647)
  ·
    refine ⟨254833050732178459689032471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169888700488118973126021647 254833050732178459689032471)
    ·
      refine ⟨382249576098267689533548707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254833050732178459689032471 382249576098267689533548707)
      ·
        refine ⟨573374364147401534300323061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382249576098267689533548707 573374364147401534300323061)
        ·
          refine ⟨53753846638818893840655287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 573374364147401534300323061 53753846638818893840655287)
          ·
            refine ⟨80630769958228340760982931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53753846638818893840655287 80630769958228340760982931)
            ·
              refine ⟨120946154937342511141474397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80630769958228340760982931 120946154937342511141474397)
              ·
                refine ⟨45354808101503441678052899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120946154937342511141474397 45354808101503441678052899)
                ·
                  refine ⟨68032212152255162517079349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45354808101503441678052899 68032212152255162517079349)
                  ·
                    refine ⟨6378019889273921485976189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68032212152255162517079349 6378019889273921485976189)
                    ·
                      refine ⟨2391757458477720557241071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6378019889273921485976189 2391757458477720557241071)
                      ·
                        rfl

theorem cell23_4657931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 3].length) (baseStart_4657931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657931 prefixEnd_4657931 := by exact prefixLift 4657931
  have htrace : WordTrace (prefixWord ++ tailWord_4657931) baseStart_4657931 baseEnd_4657931 := by
    simpa [prefixWord, tailWord_4657931, baseEnd_4657931] using wordTrace_append hprefix tailTrace_4657931
  have hstable : (prefixWord ++ tailWord_4657931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657931).length < 2 ^ (prefixWord ++ tailWord_4657931).sum := by decide
  have hdescent : baseEnd_4657931 < baseStart_4657931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4657972 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 5]
def baseStart_4657972 : Nat := 118140960795 + 4657972 * 2 ^ 59
def prefixEnd_4657972 : Nat := 4983230072969 + 3 ^ 40 * 4657972 * 2
def baseEnd_4657972 : Nat := 265753167909394988536487

theorem tailTrace_4657972 : CollatzResearch.WordTrace tailWord_4657972 prefixEnd_4657972 265753167909394988536487 := by
  unfold tailWord_4657972
  simp only [CollatzResearch.WordTrace]
  refine ⟨84945097940485218564132085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113260130587313624752176113 84945097940485218564132085)
  ·
    refine ⟨7963602931920489240387383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84945097940485218564132085 7963602931920489240387383)
    ·
      refine ⟨11945404397880733860581075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7963602931920489240387383 11945404397880733860581075)
      ·
        refine ⟨17918106596821100790871613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11945404397880733860581075 17918106596821100790871613)
        ·
          refine ⟨6719289973807912796576855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17918106596821100790871613 6719289973807912796576855)
          ·
            refine ⟨10078934960711869194865283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719289973807912796576855 10078934960711869194865283)
            ·
              refine ⟨15118402441067803792297925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078934960711869194865283 15118402441067803792297925)
              ·
                refine ⟨2834700457700213211055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15118402441067803792297925 2834700457700213211055861)
                ·
                  refine ⟨265753167909394988536487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2834700457700213211055861 265753167909394988536487)
                  ·
                    rfl

theorem cell23_4657972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_4657972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4657972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4657972 prefixEnd_4657972 := by exact prefixLift 4657972
  have htrace : WordTrace (prefixWord ++ tailWord_4657972) baseStart_4657972 baseEnd_4657972 := by
    simpa [prefixWord, tailWord_4657972, baseEnd_4657972] using wordTrace_append hprefix tailTrace_4657972
  have hstable : (prefixWord ++ tailWord_4657972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4657972).length < 2 ^ (prefixWord ++ tailWord_4657972).sum := by decide
  have hdescent : baseEnd_4657972 < baseStart_4657972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4657972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658065 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 2, 3, 2]
def baseStart_4658065 : Nat := 118140960795 + 4658065 * 2 ^ 59
def prefixEnd_4658065 : Nat := 4983230072969 + 3 ^ 40 * 4658065 * 2
def baseEnd_4658065 : Nat := 2391826264885423032965455

theorem tailTrace_4658065 : CollatzResearch.WordTrace tailWord_4658065 prefixEnd_4658065 2391826264885423032965455 := by
  unfold tailWord_4658065
  simp only [CollatzResearch.WordTrace]
  refine ⟨169893587869633514011399649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113262391913089009340933099 169893587869633514011399649)
  ·
    refine ⟨127420190902225135508549737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169893587869633514011399649 127420190902225135508549737)
    ·
      refine ⟨95565143176668851631412303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127420190902225135508549737 95565143176668851631412303)
      ·
        refine ⟨143347714765003277447118455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95565143176668851631412303 143347714765003277447118455)
        ·
          refine ⟨215021572147504916170677683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143347714765003277447118455 215021572147504916170677683)
          ·
            refine ⟨322532358221257374256016525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215021572147504916170677683 322532358221257374256016525)
            ·
              refine ⟨120949634332971515346006197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322532358221257374256016525 120949634332971515346006197)
              ·
                refine ⟨11339028218716079563688081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120949634332971515346006197 11339028218716079563688081)
                ·
                  refine ⟨8504271164037059672766061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11339028218716079563688081 8504271164037059672766061)
                  ·
                    refine ⟨3189101686513897377287273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8504271164037059672766061 3189101686513897377287273)
                    ·
                      refine ⟨2391826264885423032965455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189101686513897377287273 2391826264885423032965455)
                      ·
                        rfl

theorem cell23_4658065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_4658065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658065 prefixEnd_4658065 := by exact prefixLift 4658065
  have htrace : WordTrace (prefixWord ++ tailWord_4658065) baseStart_4658065 baseEnd_4658065 := by
    simpa [prefixWord, tailWord_4658065, baseEnd_4658065] using wordTrace_append hprefix tailTrace_4658065
  have hstable : (prefixWord ++ tailWord_4658065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658065).length < 2 ^ (prefixWord ++ tailWord_4658065).sum := by decide
  have hdescent : baseEnd_4658065 < baseStart_4658065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658066 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_4658066 : Nat := 118140960795 + 4658066 * 2 ^ 59
def prefixEnd_4658066 : Nat := 4983230072969 + 3 ^ 40 * 4658066 * 2
def baseEnd_4658066 : Nat := 797275592788692509684317

theorem tailTrace_4658066 : CollatzResearch.WordTrace tailWord_4658066 prefixEnd_4658066 797275592788692509684317 := by
  unfold tailWord_4658066
  simp only [CollatzResearch.WordTrace]
  refine ⟨42473406085657472795546513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113262416228419927454790701 42473406085657472795546513)
  ·
    refine ⟨31855054564243104596659885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42473406085657472795546513 31855054564243104596659885)
    ·
      refine ⟨11945645461591164223747457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31855054564243104596659885 11945645461591164223747457)
      ·
        refine ⟨8959234096193373167810593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11945645461591164223747457 8959234096193373167810593)
        ·
          refine ⟨6719425572145029875857945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8959234096193373167810593 6719425572145029875857945)
          ·
            refine ⟨5039569179108772406893459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6719425572145029875857945 5039569179108772406893459)
            ·
              refine ⟨7559353768663158610340189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039569179108772406893459 7559353768663158610340189)
              ·
                refine ⟨2834757663248684478877571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7559353768663158610340189 2834757663248684478877571)
                ·
                  refine ⟨4252136494873026718316357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834757663248684478877571 4252136494873026718316357)
                  ·
                    refine ⟨797275592788692509684317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4252136494873026718316357 797275592788692509684317)
                    ·
                      rfl

theorem cell23_4658066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_4658066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658066 prefixEnd_4658066 := by exact prefixLift 4658066
  have htrace : WordTrace (prefixWord ++ tailWord_4658066) baseStart_4658066 baseEnd_4658066 := by
    simpa [prefixWord, tailWord_4658066, baseEnd_4658066] using wordTrace_append hprefix tailTrace_4658066
  have hstable : (prefixWord ++ tailWord_4658066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658066).length < 2 ^ (prefixWord ++ tailWord_4658066).sum := by decide
  have hdescent : baseEnd_4658066 < baseStart_4658066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658082 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_4658082 : Nat := 118140960795 + 4658082 * 2 ^ 59
def prefixEnd_4658082 : Nat := 4983230072969 + 3 ^ 40 * 4658082 * 2
def baseEnd_4658082 : Nat := 2391834994056549466452877

theorem tailTrace_4658082 : CollatzResearch.WordTrace tailWord_4658082 prefixEnd_4658082 2391834994056549466452877 := by
  unfold tailWord_4658082
  simp only [CollatzResearch.WordTrace]
  refine ⟨42473551977642981478692125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113262805273714617276512333 42473551977642981478692125)
  ·
    refine ⟨15927581991616118054509547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42473551977642981478692125 15927581991616118054509547)
    ·
      refine ⟨23891372987424177081764321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15927581991616118054509547 23891372987424177081764321)
      ·
        refine ⟨17918529740568132811323241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23891372987424177081764321 17918529740568132811323241)
        ·
          refine ⟨13438897305426099608492431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17918529740568132811323241 13438897305426099608492431)
          ·
            refine ⟨20158345958139149412738647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13438897305426099608492431 20158345958139149412738647)
            ·
              refine ⟨30237518937208724119107971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20158345958139149412738647 30237518937208724119107971)
              ·
                refine ⟨45356278405813086178661957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30237518937208724119107971 45356278405813086178661957)
                ·
                  refine ⟨8504302201089953658499117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45356278405813086178661957 8504302201089953658499117)
                  ·
                    refine ⟨3189113325408732621937169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8504302201089953658499117 3189113325408732621937169)
                    ·
                      refine ⟨2391834994056549466452877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189113325408732621937169 2391834994056549466452877)
                      ·
                        rfl

theorem cell23_4658082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_4658082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658082 prefixEnd_4658082 := by exact prefixLift 4658082
  have htrace : WordTrace (prefixWord ++ tailWord_4658082) baseStart_4658082 baseEnd_4658082 := by
    simpa [prefixWord, tailWord_4658082, baseEnd_4658082] using wordTrace_append hprefix tailTrace_4658082
  have hstable : (prefixWord ++ tailWord_4658082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658082).length < 2 ^ (prefixWord ++ tailWord_4658082).sum := by decide
  have hdescent : baseEnd_4658082 < baseStart_4658082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658089 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 1, 1, 3]
def baseStart_4658089 : Nat := 118140960795 + 4658089 * 2 ^ 59
def prefixEnd_4658089 : Nat := 4983230072969 + 3 ^ 40 * 4658089 * 2
def baseEnd_4658089 : Nat := 2391838588421130939065345

theorem tailTrace_4658089 : CollatzResearch.WordTrace tailWord_4658089 prefixEnd_4658089 2391838588421130939065345 := by
  unfold tailWord_4658089
  simp only [CollatzResearch.WordTrace]
  refine ⟨169894463221546566110273321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113262975481031044073515547 169894463221546566110273321)
  ·
    refine ⟨127420847416159924582704991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169894463221546566110273321 127420847416159924582704991)
    ·
      refine ⟨191131271124239886874057487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127420847416159924582704991 191131271124239886874057487)
      ·
        refine ⟨286696906686359830311086231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191131271124239886874057487 286696906686359830311086231)
        ·
          refine ⟨430045360029539745466629347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286696906686359830311086231 430045360029539745466629347)
          ·
            refine ⟨645068040044309618199944021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430045360029539745466629347 645068040044309618199944021)
            ·
              refine ⟨3779695547134626669140297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 645068040044309618199944021 3779695547134626669140297)
              ·
                refine ⟨2834771660350970001855223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779695547134626669140297 2834771660350970001855223)
                ·
                  refine ⟨4252157490526455002782835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834771660350970001855223 4252157490526455002782835)
                  ·
                    refine ⟨6378236235789682504174253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4252157490526455002782835 6378236235789682504174253)
                    ·
                      refine ⟨2391838588421130939065345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6378236235789682504174253 2391838588421130939065345)
                      ·
                        rfl

theorem cell23_4658089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 1, 3].length) (baseStart_4658089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658089 prefixEnd_4658089 := by exact prefixLift 4658089
  have htrace : WordTrace (prefixWord ++ tailWord_4658089) baseStart_4658089 baseEnd_4658089 := by
    simpa [prefixWord, tailWord_4658089, baseEnd_4658089] using wordTrace_append hprefix tailTrace_4658089
  have hstable : (prefixWord ++ tailWord_4658089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658089).length < 2 ^ (prefixWord ++ tailWord_4658089).sum := by decide
  have hdescent : baseEnd_4658089 < baseStart_4658089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658098 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_4658098 : Nat := 118140960795 + 4658098 * 2 ^ 59
def prefixEnd_4658098 : Nat := 4983230072969 + 3 ^ 40 * 4658098 * 2
def baseEnd_4658098 : Nat := 2391843209747021403852803

theorem tailTrace_4658098 : CollatzResearch.WordTrace tailWord_4658098 prefixEnd_4658098 2391843209747021403852803 := by
  unfold tailWord_4658098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42473697869628490161837737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113263194319009307098233965 42473697869628490161837737)
  ·
    refine ⟨31855273402221367621378303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42473697869628490161837737 31855273402221367621378303)
    ·
      refine ⟨47782910103332051432067455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31855273402221367621378303 47782910103332051432067455)
      ·
        refine ⟨71674365154998077148101183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47782910103332051432067455 71674365154998077148101183)
        ·
          refine ⟨107511547732497115722151775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71674365154998077148101183 107511547732497115722151775)
          ·
            refine ⟨161267321598745673583227663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107511547732497115722151775 161267321598745673583227663)
            ·
              refine ⟨241900982398118510374841495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161267321598745673583227663 241900982398118510374841495)
              ·
                refine ⟨362851473597177765562262243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241900982398118510374841495 362851473597177765562262243)
                ·
                  refine ⟨544277210395766648343393365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362851473597177765562262243 544277210395766648343393365)
                  ·
                    refine ⟨6378248559325390410274141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 544277210395766648343393365 6378248559325390410274141)
                    ·
                      refine ⟨2391843209747021403852803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6378248559325390410274141 2391843209747021403852803)
                      ·
                        rfl

theorem cell23_4658098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_4658098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658098 prefixEnd_4658098 := by exact prefixLift 4658098
  have htrace : WordTrace (prefixWord ++ tailWord_4658098) baseStart_4658098 baseEnd_4658098 := by
    simpa [prefixWord, tailWord_4658098, baseEnd_4658098] using wordTrace_append hprefix tailTrace_4658098
  have hstable : (prefixWord ++ tailWord_4658098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658098).length < 2 ^ (prefixWord ++ tailWord_4658098).sum := by decide
  have hdescent : baseEnd_4658098 < baseStart_4658098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658109 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_4658109 : Nat := 118140960795 + 4658109 * 2 ^ 59
def prefixEnd_4658109 : Nat := 4983230072969 + 3 ^ 40 * 4658109 * 2
def baseEnd_4658109 : Nat := 797282952678073620271751

theorem tailTrace_4658109 : CollatzResearch.WordTrace tailWord_4658109 prefixEnd_4658109 797282952678073620271751 := by
  unfold tailWord_4658109
  simp only [CollatzResearch.WordTrace]
  refine ⟨169895192681474109526001381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113263461787649406350667587 169895192681474109526001381)
  ·
    refine ⟨31855348627776395536125259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169895192681474109526001381 31855348627776395536125259)
    ·
      refine ⟨47783022941664593304187889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31855348627776395536125259 47783022941664593304187889)
      ·
        refine ⟨35837267206248444978140917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47783022941664593304187889 35837267206248444978140917)
        ·
          refine ⟨3359743800585791716700711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35837267206248444978140917 3359743800585791716700711)
          ·
            refine ⟨5039615700878687575051067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359743800585791716700711 5039615700878687575051067)
            ·
              refine ⟨7559423551318031362576601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039615700878687575051067 7559423551318031362576601)
              ·
                refine ⟨5669567663488523521932451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7559423551318031362576601 5669567663488523521932451)
                ·
                  refine ⟨8504351495232785282898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669567663488523521932451 8504351495232785282898677)
                  ·
                    refine ⟨797282952678073620271751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8504351495232785282898677 797282952678073620271751)
                    ·
                      rfl

theorem cell23_4658109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_4658109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658109 prefixEnd_4658109 := by exact prefixLift 4658109
  have htrace : WordTrace (prefixWord ++ tailWord_4658109) baseStart_4658109 baseEnd_4658109 := by
    simpa [prefixWord, tailWord_4658109, baseEnd_4658109] using wordTrace_append hprefix tailTrace_4658109
  have hstable : (prefixWord ++ tailWord_4658109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658109).length < 2 ^ (prefixWord ++ tailWord_4658109).sum := by decide
  have hdescent : baseEnd_4658109 < baseStart_4658109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658112 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4]
def baseStart_4658112 : Nat := 118140960795 + 4658112 * 2 ^ 59
def prefixEnd_4658112 : Nat := 4983230072969 + 3 ^ 40 * 4658112 * 2
def baseEnd_4658112 : Nat := 2391850398476184349077739

theorem tailTrace_4658112 : CollatzResearch.WordTrace tailWord_4658112 prefixEnd_4658112 2391850398476184349077739 := by
  unfold tailWord_4658112
  simp only [CollatzResearch.WordTrace]
  refine ⟨84947651050231620519180295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113263534733642160692240393 84947651050231620519180295)
  ·
    refine ⟨127421476575347430778770443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84947651050231620519180295 127421476575347430778770443)
    ·
      refine ⟨191132214863021146168155665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127421476575347430778770443 191132214863021146168155665)
      ·
        refine ⟨143349161147265859626116749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191132214863021146168155665 143349161147265859626116749)
        ·
          refine ⟨53755935430224697359793781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143349161147265859626116749 53755935430224697359793781)
          ·
            refine ⟨5039618946583565377480667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53755935430224697359793781 5039618946583565377480667)
            ·
              refine ⟨7559428419875348066221001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039618946583565377480667 7559428419875348066221001)
              ·
                refine ⟨5669571314906511049665751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7559428419875348066221001 5669571314906511049665751)
                ·
                  refine ⟨8504356972359766574498627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669571314906511049665751 8504356972359766574498627)
                  ·
                    refine ⟨12756535458539649861747941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8504356972359766574498627 12756535458539649861747941)
                    ·
                      refine ⟨2391850398476184349077739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12756535458539649861747941 2391850398476184349077739)
                      ·
                        rfl

theorem cell23_4658112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_4658112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658112 prefixEnd_4658112 := by exact prefixLift 4658112
  have htrace : WordTrace (prefixWord ++ tailWord_4658112) baseStart_4658112 baseEnd_4658112 := by
    simpa [prefixWord, tailWord_4658112, baseEnd_4658112] using wordTrace_append hprefix tailTrace_4658112
  have hstable : (prefixWord ++ tailWord_4658112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658112).length < 2 ^ (prefixWord ++ tailWord_4658112).sum := by decide
  have hdescent : baseEnd_4658112 < baseStart_4658112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658116 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4658116 : Nat := 118140960795 + 4658116 * 2 ^ 59
def prefixEnd_4658116 : Nat := 4983230072969 + 3 ^ 40 * 4658116 * 2
def baseEnd_4658116 : Nat := 2391852452398802333427721

theorem tailTrace_4658116 : CollatzResearch.WordTrace tailWord_4658116 prefixEnd_4658116 2391852452398802333427721 := by
  unfold tailWord_4658116
  simp only [CollatzResearch.WordTrace]
  refine ⟨84947723996224374860753101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113263631994965833147670801 84947723996224374860753101)
  ·
    refine ⟨31855396498584140572782413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84947723996224374860753101 31855396498584140572782413)
    ·
      refine ⟨11945773686969052714793405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31855396498584140572782413 11945773686969052714793405)
      ·
        refine ⟨4479665132613394768047527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11945773686969052714793405 4479665132613394768047527)
        ·
          refine ⟨6719497698920092152071291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479665132613394768047527 6719497698920092152071291)
          ·
            refine ⟨10079246548380138228106937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719497698920092152071291 10079246548380138228106937)
            ·
              refine ⟨7559434911285103671080203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10079246548380138228106937 7559434911285103671080203)
              ·
                refine ⟨11339152366927655506620305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7559434911285103671080203 11339152366927655506620305)
                ·
                  refine ⟨8504364275195741629965229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11339152366927655506620305 8504364275195741629965229)
                  ·
                    refine ⟨3189136603198403111236961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8504364275195741629965229 3189136603198403111236961)
                    ·
                      refine ⟨2391852452398802333427721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189136603198403111236961 2391852452398802333427721)
                      ·
                        rfl

theorem cell23_4658116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4658116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658116 prefixEnd_4658116 := by exact prefixLift 4658116
  have htrace : WordTrace (prefixWord ++ tailWord_4658116) baseStart_4658116 baseEnd_4658116 := by
    simpa [prefixWord, tailWord_4658116, baseEnd_4658116] using wordTrace_append hprefix tailTrace_4658116
  have hstable : (prefixWord ++ tailWord_4658116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658116).length < 2 ^ (prefixWord ++ tailWord_4658116).sum := by decide
  have hdescent : baseEnd_4658116 < baseStart_4658116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658129 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 1, 2, 2]
def baseStart_4658129 : Nat := 118140960795 + 4658129 * 2 ^ 59
def prefixEnd_4658129 : Nat := 4983230072969 + 3 ^ 40 * 4658129 * 2
def baseEnd_4658129 : Nat := 2391859127647310782565161

theorem tailTrace_4658129 : CollatzResearch.WordTrace tailWord_4658129 prefixEnd_4658129 2391859127647310782565161 := by
  unfold tailWord_4658129
  simp only [CollatzResearch.WordTrace]
  refine ⟨169895922141401652941729441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113263948094267768627819627 169895922141401652941729441)
  ·
    refine ⟨127421941606051239706297081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169895922141401652941729441 127421941606051239706297081)
    ·
      refine ⟨95566456204538429779722811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127421941606051239706297081 95566456204538429779722811)
      ·
        refine ⟨143349684306807644669584217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95566456204538429779722811 143349684306807644669584217)
        ·
          refine ⟨107512263230105733502188163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143349684306807644669584217 107512263230105733502188163)
          ·
            refine ⟨161268394845158600253282245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107512263230105733502188163 161268394845158600253282245)
            ·
              refine ⟨30237824033467237547490421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161268394845158600253282245 30237824033467237547490421)
              ·
                refine ⟨2834796003137553520077227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30237824033467237547490421 2834796003137553520077227)
                ·
                  refine ⟨4252194004706330280115841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834796003137553520077227 4252194004706330280115841)
                  ·
                    refine ⟨3189145503529747710086881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4252194004706330280115841 3189145503529747710086881)
                    ·
                      refine ⟨2391859127647310782565161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189145503529747710086881 2391859127647310782565161)
                      ·
                        rfl

theorem cell23_4658129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_4658129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658129 prefixEnd_4658129 := by exact prefixLift 4658129
  have htrace : WordTrace (prefixWord ++ tailWord_4658129) baseStart_4658129 baseEnd_4658129 := by
    simpa [prefixWord, tailWord_4658129, baseEnd_4658129] using wordTrace_append hprefix tailTrace_4658129
  have hstable : (prefixWord ++ tailWord_4658129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658129).length < 2 ^ (prefixWord ++ tailWord_4658129).sum := by decide
  have hdescent : baseEnd_4658129 < baseStart_4658129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658132 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_4658132 : Nat := 118140960795 + 4658132 * 2 ^ 59
def prefixEnd_4658132 : Nat := 4983230072969 + 3 ^ 40 * 4658132 * 2
def baseEnd_4658132 : Nat := 2391860668089274270827647

theorem tailTrace_4658132 : CollatzResearch.WordTrace tailWord_4658132 prefixEnd_4658132 2391860668089274270827647 := by
  unfold tailWord_4658132
  simp only [CollatzResearch.WordTrace]
  refine ⟨84948015780195392227044325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113264021040260522969392433 84948015780195392227044325)
  ·
    refine ⟨15927752958786636042570811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84948015780195392227044325 15927752958786636042570811)
    ·
      refine ⟨23891629438179954063856217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15927752958786636042570811 23891629438179954063856217)
      ·
        refine ⟨17918722078634965547892163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23891629438179954063856217 17918722078634965547892163)
        ·
          refine ⟨26878083117952448321838245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17918722078634965547892163 26878083117952448321838245)
          ·
            refine ⟨5039640584616084060344671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26878083117952448321838245 5039640584616084060344671)
            ·
              refine ⟨7559460876924126090517007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039640584616084060344671 7559460876924126090517007)
              ·
                refine ⟨11339191315386189135775511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7559460876924126090517007 11339191315386189135775511)
                ·
                  refine ⟨17008786973079283703663267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11339191315386189135775511 17008786973079283703663267)
                  ·
                    refine ⟨25513180459618925555494901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17008786973079283703663267 25513180459618925555494901)
                    ·
                      refine ⟨2391860668089274270827647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25513180459618925555494901 2391860668089274270827647)
                      ·
                        rfl

theorem cell23_4658132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_4658132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658132 prefixEnd_4658132 := by exact prefixLift 4658132
  have htrace : WordTrace (prefixWord ++ tailWord_4658132) baseStart_4658132 baseEnd_4658132 := by
    simpa [prefixWord, tailWord_4658132, baseEnd_4658132] using wordTrace_append hprefix tailTrace_4658132
  have hstable : (prefixWord ++ tailWord_4658132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658132).length < 2 ^ (prefixWord ++ tailWord_4658132).sum := by decide
  have hdescent : baseEnd_4658132 < baseStart_4658132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658168 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_4658168 : Nat := 118140960795 + 4658168 * 2 ^ 59
def prefixEnd_4658168 : Nat := 4983230072969 + 3 ^ 40 * 4658168 * 2
def baseEnd_4658168 : Nat := 2391879153392836129977481

theorem tailTrace_4658168 : CollatzResearch.WordTrace tailWord_4658168 prefixEnd_4658168 2391879153392836129977481 := by
  unfold tailWord_4658168
  simp only [CollatzResearch.WordTrace]
  refine ⟨84948672294130181301199579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113264896392173575068266105 84948672294130181301199579)
  ·
    refine ⟨127423008441195271951799369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84948672294130181301199579 127423008441195271951799369)
    ·
      refine ⟨95567256330896453963849527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127423008441195271951799369 95567256330896453963849527)
      ·
        refine ⟨143350884496344680945774291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95567256330896453963849527 143350884496344680945774291)
        ·
          refine ⟨215026326744517021418661437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143350884496344680945774291 215026326744517021418661437)
          ·
            refine ⟨80634872529193883031998039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215026326744517021418661437 80634872529193883031998039)
            ·
              refine ⟨120952308793790824547997059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80634872529193883031998039 120952308793790824547997059)
              ·
                refine ⟨181428463190686236821995589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120952308793790824547997059 181428463190686236821995589)
                ·
                  refine ⟨34017836848253669404124173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181428463190686236821995589 34017836848253669404124173)
                  ·
                    refine ⟨12756688818095126026546565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34017836848253669404124173 12756688818095126026546565)
                    ·
                      refine ⟨2391879153392836129977481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12756688818095126026546565 2391879153392836129977481)
                      ·
                        rfl

theorem cell23_4658168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_4658168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658168 prefixEnd_4658168 := by exact prefixLift 4658168
  have htrace : WordTrace (prefixWord ++ tailWord_4658168) baseStart_4658168 baseEnd_4658168 := by
    simpa [prefixWord, tailWord_4658168, baseEnd_4658168] using wordTrace_append hprefix tailTrace_4658168
  have hstable : (prefixWord ++ tailWord_4658168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658168).length < 2 ^ (prefixWord ++ tailWord_4658168).sum := by decide
  have hdescent : baseEnd_4658168 < baseStart_4658168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658172 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_4658172 : Nat := 118140960795 + 4658172 * 2 ^ 59
def prefixEnd_4658172 : Nat := 4983230072969 + 3 ^ 40 * 4658172 * 2
def baseEnd_4658172 : Nat := 2391881207315454114327463

theorem tailTrace_4658172 : CollatzResearch.WordTrace tailWord_4658172 prefixEnd_4658172 2391881207315454114327463 := by
  unfold tailWord_4658172
  simp only [CollatzResearch.WordTrace]
  refine ⟨84948745240122935642772385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113264993653497247523696513 84948745240122935642772385)
  ·
    refine ⟨63711558930092201732079289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84948745240122935642772385 63711558930092201732079289)
    ·
      refine ⟨47783669197569151299059467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63711558930092201732079289 47783669197569151299059467)
      ·
        refine ⟨71675503796353726948589201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47783669197569151299059467 71675503796353726948589201)
        ·
          refine ⟨53756627847265295211441901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71675503796353726948589201 53756627847265295211441901)
          ·
            refine ⟨20158735442724485704290713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53756627847265295211441901 20158735442724485704290713)
            ·
              refine ⟨15119051582043364278218035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20158735442724485704290713 15119051582043364278218035)
              ·
                refine ⟨22678577373065046417327053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15119051582043364278218035 22678577373065046417327053)
                ·
                  refine ⟨8504466514899392406497645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22678577373065046417327053 8504466514899392406497645)
                  ·
                    refine ⟨3189174943087272152436617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8504466514899392406497645 3189174943087272152436617)
                    ·
                      refine ⟨2391881207315454114327463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189174943087272152436617 2391881207315454114327463)
                      ·
                        rfl

theorem cell23_4658172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_4658172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658172 prefixEnd_4658172 := by exact prefixLift 4658172
  have htrace : WordTrace (prefixWord ++ tailWord_4658172) baseStart_4658172 baseEnd_4658172 := by
    simpa [prefixWord, tailWord_4658172, baseEnd_4658172] using wordTrace_append hprefix tailTrace_4658172
  have hstable : (prefixWord ++ tailWord_4658172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658172).length < 2 ^ (prefixWord ++ tailWord_4658172).sum := by decide
  have hdescent : baseEnd_4658172 < baseStart_4658172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658270 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4658270 : Nat := 118140960795 + 4658270 * 2 ^ 59
def prefixEnd_4658270 : Nat := 4983230072969 + 3 ^ 40 * 4658270 * 2
def baseEnd_4658270 : Nat := 2391931528419594730902013

theorem tailTrace_4658270 : CollatzResearch.WordTrace tailWord_4658270 prefixEnd_4658270 2391931528419594730902013 := by
  unfold tailWord_4658270
  simp only [CollatzResearch.WordTrace]
  refine ⟨21237633104236354252826533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113267376555927222681741509 21237633104236354252826533)
  ·
    refine ⟨3982056207044316422404975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21237633104236354252826533 3982056207044316422404975)
    ·
      refine ⟨5973084310566474633607463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3982056207044316422404975 5973084310566474633607463)
      ·
        refine ⟨8959626465849711950411195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5973084310566474633607463 8959626465849711950411195)
        ·
          refine ⟨13439439698774567925616793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959626465849711950411195 13439439698774567925616793)
          ·
            refine ⟨10079579774080925944212595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13439439698774567925616793 10079579774080925944212595)
            ·
              refine ⟨15119369661121388916318893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10079579774080925944212595 15119369661121388916318893)
              ·
                refine ⟨5669763622920520843619585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15119369661121388916318893 5669763622920520843619585)
                ·
                  refine ⟨4252322717190390632714689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5669763622920520843619585 4252322717190390632714689)
                  ·
                    refine ⟨3189242037892792974536017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4252322717190390632714689 3189242037892792974536017)
                    ·
                      refine ⟨2391931528419594730902013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189242037892792974536017 2391931528419594730902013)
                      ·
                        rfl

theorem cell23_4658270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4658270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658270 prefixEnd_4658270 := by exact prefixLift 4658270
  have htrace : WordTrace (prefixWord ++ tailWord_4658270) baseStart_4658270 baseEnd_4658270 := by
    simpa [prefixWord, tailWord_4658270, baseEnd_4658270] using wordTrace_append hprefix tailTrace_4658270
  have hstable : (prefixWord ++ tailWord_4658270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658270).length < 2 ^ (prefixWord ++ tailWord_4658270).sum := by decide
  have hdescent : baseEnd_4658270 < baseStart_4658270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658275 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4658275 : Nat := 118140960795 + 4658275 * 2 ^ 59
def prefixEnd_4658275 : Nat := 4983230072969 + 3 ^ 40 * 4658275 * 2
def baseEnd_4658275 : Nat := 2391934095822867211339489

theorem tailTrace_4658275 : CollatzResearch.WordTrace tailWord_4658275 prefixEnd_4658275 2391934095822867211339489 := by
  unfold tailWord_4658275
  simp only [CollatzResearch.WordTrace]
  refine ⟨169901247198872719876544279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113267498132581813251029519 169901247198872719876544279)
  ·
    refine ⟨254851870798309079814816419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169901247198872719876544279 254851870798309079814816419)
    ·
      refine ⟨382277806197463619722224629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254851870798309079814816419 382277806197463619722224629)
      ·
        refine ⟨35838544331012214348958559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 382277806197463619722224629 35838544331012214348958559)
        ·
          refine ⟨53757816496518321523437839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35838544331012214348958559 53757816496518321523437839)
          ·
            refine ⟨80636724744777482285156759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53757816496518321523437839 80636724744777482285156759)
            ·
              refine ⟨120955087117166223427735139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80636724744777482285156759 120955087117166223427735139)
              ·
                refine ⟨181432630675749335141602709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120955087117166223427735139 181432630675749335141602709)
                ·
                  refine ⟨8504654562925750084762627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181432630675749335141602709 8504654562925750084762627)
                  ·
                    refine ⟨12756981844388625127143941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8504654562925750084762627 12756981844388625127143941)
                    ·
                      refine ⟨2391934095822867211339489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12756981844388625127143941 2391934095822867211339489)
                      ·
                        rfl

theorem cell23_4658275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4658275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658275 prefixEnd_4658275 := by exact prefixLift 4658275
  have htrace : WordTrace (prefixWord ++ tailWord_4658275) baseStart_4658275 baseEnd_4658275 := by
    simpa [prefixWord, tailWord_4658275, baseEnd_4658275] using wordTrace_append hprefix tailTrace_4658275
  have hstable : (prefixWord ++ tailWord_4658275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658275).length < 2 ^ (prefixWord ++ tailWord_4658275).sum := by decide
  have hdescent : baseEnd_4658275 < baseStart_4658275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658332 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 6]
def baseStart_4658332 : Nat := 118140960795 + 4658332 * 2 ^ 59
def prefixEnd_4658332 : Nat := 4983230072969 + 3 ^ 40 * 4658332 * 2
def baseEnd_4658332 : Nat := 265773707135574832036303

theorem tailTrace_4658332 : CollatzResearch.WordTrace tailWord_4658332 prefixEnd_4658332 265773707135574832036303 := by
  unfold tailWord_4658332
  simp only [CollatzResearch.WordTrace]
  refine ⟨84951663079833109305684625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113268884106444145740912833 84951663079833109305684625)
  ·
    refine ⟨63713747309874831979263469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84951663079833109305684625 63713747309874831979263469)
    ·
      refine ⟨23892655241203061992223801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63713747309874831979263469 23892655241203061992223801)
      ·
        refine ⟨17919491430902296494167851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23892655241203061992223801 17919491430902296494167851)
        ·
          refine ⟨26879237146353444741251777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17919491430902296494167851 26879237146353444741251777)
          ·
            refine ⟨20159427859765083555938833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26879237146353444741251777 20159427859765083555938833)
            ·
              refine ⟨15119570894823812666954125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20159427859765083555938833 15119570894823812666954125)
              ·
                refine ⟨5669839085558929750107797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15119570894823812666954125 5669839085558929750107797)
                ·
                  refine ⟨265773707135574832036303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5669839085558929750107797 265773707135574832036303)
                  ·
                    rfl

theorem cell23_4658332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_4658332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658332 prefixEnd_4658332 := by exact prefixLift 4658332
  have htrace : WordTrace (prefixWord ++ tailWord_4658332) baseStart_4658332 baseEnd_4658332 := by
    simpa [prefixWord, tailWord_4658332, baseEnd_4658332] using wordTrace_append hprefix tailTrace_4658332
  have hstable : (prefixWord ++ tailWord_4658332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658332).length < 2 ^ (prefixWord ++ tailWord_4658332).sum := by decide
  have hdescent : baseEnd_4658332 < baseStart_4658332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658346 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4658346 : Nat := 118140960795 + 4658346 * 2 ^ 59
def prefixEnd_4658346 : Nat := 4983230072969 + 3 ^ 40 * 4658346 * 2
def baseEnd_4658346 : Nat := 2391970552949336433551663

theorem tailTrace_4658346 : CollatzResearch.WordTrace tailWord_4658346 prefixEnd_4658346 2391970552949336433551663 := by
  unfold tailWord_4658346
  simp only [CollatzResearch.WordTrace]
  refine ⟨42475959195403874750594723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113269224521076999334919261 42475959195403874750594723)
  ·
    refine ⟨63713938793105812125892085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42475959195403874750594723 63713938793105812125892085)
    ·
      refine ⟨5973181761853669886802383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63713938793105812125892085 5973181761853669886802383)
      ·
        refine ⟨8959772642780504830203575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5973181761853669886802383 8959772642780504830203575)
        ·
          refine ⟨13439658964170757245305363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959772642780504830203575 13439658964170757245305363)
          ·
            refine ⟨20159488446256135867958045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13439658964170757245305363 20159488446256135867958045)
            ·
              refine ⟨7559808167346050950484267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20159488446256135867958045 7559808167346050950484267)
              ·
                refine ⟨11339712251019076425726401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7559808167346050950484267 11339712251019076425726401)
                ·
                  refine ⟨8504784188264307319294801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11339712251019076425726401 8504784188264307319294801)
                  ·
                    refine ⟨6378588141198230489471101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8504784188264307319294801 6378588141198230489471101)
                    ·
                      refine ⟨2391970552949336433551663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6378588141198230489471101 2391970552949336433551663)
                      ·
                        rfl

theorem cell23_4658346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4658346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658346 prefixEnd_4658346 := by exact prefixLift 4658346
  have htrace : WordTrace (prefixWord ++ tailWord_4658346) baseStart_4658346 baseEnd_4658346 := by
    simpa [prefixWord, tailWord_4658346, baseEnd_4658346] using wordTrace_append hprefix tailTrace_4658346
  have hstable : (prefixWord ++ tailWord_4658346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658346).length < 2 ^ (prefixWord ++ tailWord_4658346).sum := by decide
  have hdescent : baseEnd_4658346 < baseStart_4658346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658352 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 1, 5, 2]
def baseStart_4658352 : Nat := 118140960795 + 4658352 * 2 ^ 59
def prefixEnd_4658352 : Nat := 4983230072969 + 3 ^ 40 * 4658352 * 2
def baseEnd_4658352 : Nat := 2391973633833263410076635

theorem tailTrace_4658352 : CollatzResearch.WordTrace tailWord_4658352 prefixEnd_4658352 2391973633833263410076635 := by
  unfold tailWord_4658352
  simp only [CollatzResearch.WordTrace]
  refine ⟨84952027809796881013548655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113269370413062508018064873 84952027809796881013548655)
  ·
    refine ⟨127428041714695321520322983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84952027809796881013548655 127428041714695321520322983)
    ·
      refine ⟨191142062572042982280484475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127428041714695321520322983 191142062572042982280484475)
      ·
        refine ⟨286713093858064473420726713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191142062572042982280484475 286713093858064473420726713)
        ·
          refine ⟨215034820393548355065545035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286713093858064473420726713 215034820393548355065545035)
          ·
            refine ⟨322552230590322532598317553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215034820393548355065545035 322552230590322532598317553)
            ·
              refine ⟨241914172942741899448738165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322552230590322532598317553 241914172942741899448738165)
              ·
                refine ⟨22679453713382053073319203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241914172942741899448738165 22679453713382053073319203)
                ·
                  refine ⟨34019180570073079609978805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22679453713382053073319203 34019180570073079609978805)
                  ·
                    refine ⟨3189298178444351213435513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34019180570073079609978805 3189298178444351213435513)
                    ·
                      refine ⟨2391973633833263410076635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189298178444351213435513 2391973633833263410076635)
                      ·
                        rfl

theorem cell23_4658352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 5, 2].length) (baseStart_4658352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658352 prefixEnd_4658352 := by exact prefixLift 4658352
  have htrace : WordTrace (prefixWord ++ tailWord_4658352) baseStart_4658352 baseEnd_4658352 := by
    simpa [prefixWord, tailWord_4658352, baseEnd_4658352] using wordTrace_append hprefix tailTrace_4658352
  have hstable : (prefixWord ++ tailWord_4658352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658352).length < 2 ^ (prefixWord ++ tailWord_4658352).sum := by decide
  have hdescent : baseEnd_4658352 < baseStart_4658352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658375 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 3, 6]
def baseStart_4658375 : Nat := 118140960795 + 4658375 * 2 ^ 59
def prefixEnd_4658375 : Nat := 4983230072969 + 3 ^ 40 * 4658375 * 2
def baseEnd_4658375 : Nat := 797328481296105606696343

theorem tailTrace_4658375 : CollatzResearch.WordTrace tailWord_4658375 prefixEnd_4658375 797328481296105606696343 := by
  unfold tailWord_4658375
  simp only [CollatzResearch.WordTrace]
  refine ⟨169904894498510436955184579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113269929665673624636789719 169904894498510436955184579)
  ·
    refine ⟨254857341747765655432776869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169904894498510436955184579 254857341747765655432776869)
    ·
      refine ⟨47785751577706060393645663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254857341747765655432776869 47785751577706060393645663)
      ·
        refine ⟨71678627366559090590468495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47785751577706060393645663 71678627366559090590468495)
        ·
          refine ⟨107517941049838635885702743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71678627366559090590468495 107517941049838635885702743)
          ·
            refine ⟨161276911574757953828554115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107517941049838635885702743 161276911574757953828554115)
            ·
              refine ⟨241915367362136930742831173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161276911574757953828554115 241915367362136930742831173)
              ·
                refine ⟨45359131380400674514280845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241915367362136930742831173 45359131380400674514280845)
                ·
                  refine ⟨17009674267650252942855317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45359131380400674514280845 17009674267650252942855317)
                  ·
                    refine ⟨797328481296105606696343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17009674267650252942855317 797328481296105606696343)
                    ·
                      rfl

theorem cell23_4658375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_4658375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658375 prefixEnd_4658375 := by exact prefixLift 4658375
  have htrace : WordTrace (prefixWord ++ tailWord_4658375) baseStart_4658375 baseEnd_4658375 := by
    simpa [prefixWord, tailWord_4658375, baseEnd_4658375] using wordTrace_append hprefix tailTrace_4658375
  have hstable : (prefixWord ++ tailWord_4658375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658375).length < 2 ^ (prefixWord ++ tailWord_4658375).sum := by decide
  have hdescent : baseEnd_4658375 < baseStart_4658375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658376 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_4658376 : Nat := 118140960795 + 4658376 * 2 ^ 59
def prefixEnd_4658376 : Nat := 4983230072969 + 3 ^ 40 * 4658376 * 2
def baseEnd_4658376 : Nat := 2391985957368971316176525

theorem tailTrace_4658376 : CollatzResearch.WordTrace tailWord_4658376 prefixEnd_4658376 2391985957368971316176525 := by
  unfold tailWord_4658376
  simp only [CollatzResearch.WordTrace]
  refine ⟨84952465485753407062985491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113269953981004542750647321 84952465485753407062985491)
  ·
    refine ⟨127428698228630110594478237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84952465485753407062985491 127428698228630110594478237)
    ·
      refine ⟨47785761835736291472929339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127428698228630110594478237 47785761835736291472929339)
      ·
        refine ⟨71678642753604437209394009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47785761835736291472929339 71678642753604437209394009)
        ·
          refine ⟨53758982065203327907045507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71678642753604437209394009 53758982065203327907045507)
          ·
            refine ⟨80638473097804991860568261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53758982065203327907045507 80638473097804991860568261)
            ·
              refine ⟨15119713705838435973856549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80638473097804991860568261 15119713705838435973856549)
              ·
                refine ⟨2834946319844706745098103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15119713705838435973856549 2834946319844706745098103)
                ·
                  refine ⟨4252419479767060117647155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834946319844706745098103 4252419479767060117647155)
                  ·
                    refine ⟨6378629219650590176470733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4252419479767060117647155 6378629219650590176470733)
                    ·
                      refine ⟨2391985957368971316176525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6378629219650590176470733 2391985957368971316176525)
                      ·
                        rfl

theorem cell23_4658376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_4658376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658376 prefixEnd_4658376 := by exact prefixLift 4658376
  have htrace : WordTrace (prefixWord ++ tailWord_4658376) baseStart_4658376 baseEnd_4658376 := by
    simpa [prefixWord, tailWord_4658376, baseEnd_4658376] using wordTrace_append hprefix tailTrace_4658376
  have hstable : (prefixWord ++ tailWord_4658376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658376).length < 2 ^ (prefixWord ++ tailWord_4658376).sum := by decide
  have hdescent : baseEnd_4658376 < baseStart_4658376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658419 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 3]
def baseStart_4658419 : Nat := 118140960795 + 4658419 * 2 ^ 59
def prefixEnd_4658419 : Nat := 4983230072969 + 3 ^ 40 * 4658419 * 2
def baseEnd_4658419 : Nat := 2392008037037114647938827

theorem tailTrace_4658419 : CollatzResearch.WordTrace tailWord_4658419 prefixEnd_4658419 2392008037037114647938827 := by
  unfold tailWord_4658419
  simp only [CollatzResearch.WordTrace]
  refine ⟨169906499310351032469786311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113270999540234021646524207 169906499310351032469786311)
  ·
    refine ⟨254859748965526548704679467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169906499310351032469786311 254859748965526548704679467)
    ·
      refine ⟨382289623448289823057019201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254859748965526548704679467 382289623448289823057019201)
      ·
        refine ⟨286717217586217367292764401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382289623448289823057019201 286717217586217367292764401)
        ·
          refine ⟨215037913189663025469573301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286717217586217367292764401 215037913189663025469573301)
          ·
            refine ⟨20159804361530908637772497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215037913189663025469573301 20159804361530908637772497)
            ·
              refine ⟨15119853271148181478329373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20159804361530908637772497 15119853271148181478329373)
              ·
                refine ⟨5669944976680568054373515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15119853271148181478329373 5669944976680568054373515)
                ·
                  refine ⟨8504917465020852081560273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669944976680568054373515 8504917465020852081560273)
                  ·
                    refine ⟨6378688098765639061170205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8504917465020852081560273 6378688098765639061170205)
                    ·
                      refine ⟨2392008037037114647938827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6378688098765639061170205 2392008037037114647938827)
                      ·
                        rfl

theorem cell23_4658419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_4658419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658419 prefixEnd_4658419 := by exact prefixLift 4658419
  have htrace : WordTrace (prefixWord ++ tailWord_4658419) baseStart_4658419 baseEnd_4658419 := by
    simpa [prefixWord, tailWord_4658419, baseEnd_4658419] using wordTrace_append hprefix tailTrace_4658419
  have hstable : (prefixWord ++ tailWord_4658419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658419).length < 2 ^ (prefixWord ++ tailWord_4658419).sum := by decide
  have hdescent : baseEnd_4658419 < baseStart_4658419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658433 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_4658433 : Nat := 118140960795 + 4658433 * 2 ^ 59
def prefixEnd_4658433 : Nat := 4983230072969 + 3 ^ 40 * 4658433 * 2
def baseEnd_4658433 : Nat := 2392015225766277593163763

theorem tailTrace_4658433 : CollatzResearch.WordTrace tailWord_4658433 prefixEnd_4658433 2392015225766277593163763 := by
  unfold tailWord_4658433
  simp only [CollatzResearch.WordTrace]
  refine ⟨169907009932300312860795953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113271339954866875240530635 169907009932300312860795953)
  ·
    refine ⟨127430257449225234645596965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169907009932300312860795953 127430257449225234645596965)
    ·
      refine ⟨23893173271729731496049431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127430257449225234645596965 23893173271729731496049431)
      ·
        refine ⟨35839759907594597244074147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23893173271729731496049431 35839759907594597244074147)
        ·
          refine ⟨53759639861391895866111221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35839759907594597244074147 53759639861391895866111221)
          ·
            refine ⟨5039966237005490237447927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53759639861391895866111221 5039966237005490237447927)
            ·
              refine ⟨7559949355508235356171891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039966237005490237447927 7559949355508235356171891)
              ·
                refine ⟨11339924033262353034257837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7559949355508235356171891 11339924033262353034257837)
                ·
                  refine ⟨4252471512473382387846689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11339924033262353034257837 4252471512473382387846689)
                  ·
                    refine ⟨3189353634355036790885017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4252471512473382387846689 3189353634355036790885017)
                    ·
                      refine ⟨2392015225766277593163763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189353634355036790885017 2392015225766277593163763)
                      ·
                        rfl

theorem cell23_4658433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_4658433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658433 prefixEnd_4658433 := by exact prefixLift 4658433
  have htrace : WordTrace (prefixWord ++ tailWord_4658433) baseStart_4658433 baseEnd_4658433 := by
    simpa [prefixWord, tailWord_4658433, baseEnd_4658433] using wordTrace_append hprefix tailTrace_4658433
  have hstable : (prefixWord ++ tailWord_4658433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658433).length < 2 ^ (prefixWord ++ tailWord_4658433).sum := by decide
  have hdescent : baseEnd_4658433 < baseStart_4658433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658450 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4658450 : Nat := 118140960795 + 4658450 * 2 ^ 59
def prefixEnd_4658450 : Nat := 4983230072969 + 3 ^ 40 * 4658450 * 2
def baseEnd_4658450 : Nat := 2392023954937404026651185

theorem tailTrace_4658450 : CollatzResearch.WordTrace tailWord_4658450 prefixEnd_4658450 2392023954937404026651185 := by
  unfold tailWord_4658450
  simp only [CollatzResearch.WordTrace]
  refine ⟨42476907493309681191041201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113271753315492483176109869 42476907493309681191041201)
  ·
    refine ⟨31857680619982260893280901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42476907493309681191041201 31857680619982260893280901)
    ·
      refine ⟨5973315116246673917490169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31857680619982260893280901 5973315116246673917490169)
      ·
        refine ⟨4479986337185005438117627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5973315116246673917490169 4479986337185005438117627)
        ·
          refine ⟨6719979505777508157176441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479986337185005438117627 6719979505777508157176441)
          ·
            refine ⟨5039984629333131117882331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6719979505777508157176441 5039984629333131117882331)
            ·
              refine ⟨7559976943999696676823497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039984629333131117882331 7559976943999696676823497)
              ·
                refine ⟨5669982707999772507617623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7559976943999696676823497 5669982707999772507617623)
                ·
                  refine ⟨8504974061999658761426435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5669982707999772507617623 8504974061999658761426435)
                  ·
                    refine ⟨12757461092999488142139653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8504974061999658761426435 12757461092999488142139653)
                    ·
                      refine ⟨2392023954937404026651185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12757461092999488142139653 2392023954937404026651185)
                      ·
                        rfl

theorem cell23_4658450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4658450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658450 prefixEnd_4658450 := by exact prefixLift 4658450
  have htrace : WordTrace (prefixWord ++ tailWord_4658450) baseStart_4658450 baseEnd_4658450 := by
    simpa [prefixWord, tailWord_4658450, baseEnd_4658450] using wordTrace_append hprefix tailTrace_4658450
  have hstable : (prefixWord ++ tailWord_4658450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658450).length < 2 ^ (prefixWord ++ tailWord_4658450).sum := by decide
  have hdescent : baseEnd_4658450 < baseStart_4658450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658466 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_4658466 : Nat := 118140960795 + 4658466 * 2 ^ 59
def prefixEnd_4658466 : Nat := 4983230072969 + 3 ^ 40 * 4658466 * 2
def baseEnd_4658466 : Nat := 2392032170627875964051111

theorem tailTrace_4658466 : CollatzResearch.WordTrace tailWord_4658466 prefixEnd_4658466 2392032170627875964051111 := by
  unfold tailWord_4658466
  simp only [CollatzResearch.WordTrace]
  refine ⟨42477053385295189874186813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113272142360787172997831501 42477053385295189874186813)
  ·
    refine ⟨15928895019485696202820055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42477053385295189874186813 15928895019485696202820055)
    ·
      refine ⟨23893342529228544304230083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15928895019485696202820055 23893342529228544304230083)
      ·
        refine ⟨35840013793842816456345125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23893342529228544304230083 35840013793842816456345125)
        ·
          refine ⟨6720002586345528085564711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35840013793842816456345125 6720002586345528085564711)
          ·
            refine ⟨10080003879518292128347067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6720002586345528085564711 10080003879518292128347067)
            ·
              refine ⟨15120005819277438192520601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10080003879518292128347067 15120005819277438192520601)
              ·
                refine ⟨11340004364458078644390451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15120005819277438192520601 11340004364458078644390451)
                ·
                  refine ⟨17010006546687117966585677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11340004364458078644390451 17010006546687117966585677)
                  ·
                    refine ⟨6378752455007669237469629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17010006546687117966585677 6378752455007669237469629)
                    ·
                      refine ⟨2392032170627875964051111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6378752455007669237469629 2392032170627875964051111)
                      ·
                        rfl

theorem cell23_4658466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_4658466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658466 prefixEnd_4658466 := by exact prefixLift 4658466
  have htrace : WordTrace (prefixWord ++ tailWord_4658466) baseStart_4658466 baseEnd_4658466 := by
    simpa [prefixWord, tailWord_4658466, baseEnd_4658466] using wordTrace_append hprefix tailTrace_4658466
  have hstable : (prefixWord ++ tailWord_4658466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658466).length < 2 ^ (prefixWord ++ tailWord_4658466).sum := by decide
  have hdescent : baseEnd_4658466 < baseStart_4658466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658512 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 7]
def baseStart_4658512 : Nat := 118140960795 + 4658512 * 2 ^ 59
def prefixEnd_4658512 : Nat := 4983230072969 + 3 ^ 40 * 4658512 * 2
def baseEnd_4658512 : Nat := 265783976748664753786211

theorem tailTrace_4658512 : CollatzResearch.WordTrace tailWord_4658512 prefixEnd_4658512 265783976748664753786211 := by
  unfold tailWord_4658512
  simp only [CollatzResearch.WordTrace]
  refine ⟨84954945649507054676460895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113273260866009406235281193 84954945649507054676460895)
  ·
    refine ⟨127432418474260582014691343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84954945649507054676460895 127432418474260582014691343)
    ·
      refine ⟨191148627711390873022037015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127432418474260582014691343 191148627711390873022037015)
      ·
        refine ⟨286722941567086309533055523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191148627711390873022037015 286722941567086309533055523)
        ·
          refine ⟨430084412350629464299583285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286722941567086309533055523 430084412350629464299583285)
          ·
            refine ⟨40320413657871512278085933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 430084412350629464299583285 40320413657871512278085933)
            ·
              refine ⟨15120155121701817104282225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40320413657871512278085933 15120155121701817104282225)
              ·
                refine ⟨11340116341276362828211669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15120155121701817104282225 11340116341276362828211669)
                ·
                  refine ⟨265783976748664753786211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11340116341276362828211669 265783976748664753786211)
                  ·
                    rfl

theorem cell23_4658512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_4658512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658512 prefixEnd_4658512 := by exact prefixLift 4658512
  have htrace : WordTrace (prefixWord ++ tailWord_4658512) baseStart_4658512 baseEnd_4658512 := by
    simpa [prefixWord, tailWord_4658512, baseEnd_4658512] using wordTrace_append hprefix tailTrace_4658512
  have hstable : (prefixWord ++ tailWord_4658512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658512).length < 2 ^ (prefixWord ++ tailWord_4658512).sum := by decide
  have hdescent : baseEnd_4658512 < baseStart_4658512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658540 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 2, 2, 2]
def baseStart_4658540 : Nat := 118140960795 + 4658540 * 2 ^ 59
def prefixEnd_4658540 : Nat := 4983230072969 + 3 ^ 40 * 4658540 * 2
def baseEnd_4658540 : Nat := 2392070168196308674525771

theorem tailTrace_4658540 : CollatzResearch.WordTrace tailWord_4658540 prefixEnd_4658540 2392070168196308674525771 := by
  unfold tailWord_4658540
  simp only [CollatzResearch.WordTrace]
  refine ⟨84955456271456335067470537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113273941695275113423294049 84955456271456335067470537)
  ·
    refine ⟨63716592203592251300602903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84955456271456335067470537 63716592203592251300602903)
    ·
      refine ⟨95574888305388376950904355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63716592203592251300602903 95574888305388376950904355)
      ·
        refine ⟨143362332458082565426356533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95574888305388376950904355 143362332458082565426356533)
        ·
          refine ⟨13440218667945240508720925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143362332458082565426356533 13440218667945240508720925)
          ·
            refine ⟨5040082000479465190770347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13440218667945240508720925 5040082000479465190770347)
            ·
              refine ⟨7560123000719197786155521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5040082000479465190770347 7560123000719197786155521)
              ·
                refine ⟨5670092250539398339616641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7560123000719197786155521 5670092250539398339616641)
                ·
                  refine ⟨4252569187904548754712481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5670092250539398339616641 4252569187904548754712481)
                  ·
                    refine ⟨3189426890928411566034361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4252569187904548754712481 3189426890928411566034361)
                    ·
                      refine ⟨2392070168196308674525771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189426890928411566034361 2392070168196308674525771)
                      ·
                        rfl

theorem cell23_4658540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_4658540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658540 prefixEnd_4658540 := by exact prefixLift 4658540
  have htrace : WordTrace (prefixWord ++ tailWord_4658540) baseStart_4658540 baseEnd_4658540 := by
    simpa [prefixWord, tailWord_4658540, baseEnd_4658540] using wordTrace_append hprefix tailTrace_4658540
  have hstable : (prefixWord ++ tailWord_4658540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658540).length < 2 ^ (prefixWord ++ tailWord_4658540).sum := by decide
  have hdescent : baseEnd_4658540 < baseStart_4658540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658572 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_4658572 : Nat := 118140960795 + 4658572 * 2 ^ 59
def prefixEnd_4658572 : Nat := 4983230072969 + 3 ^ 40 * 4658572 * 2
def baseEnd_4658572 : Nat := 797362199859084183108541

theorem tailTrace_4658572 : CollatzResearch.WordTrace tailWord_4658572 prefixEnd_4658572 797362199859084183108541 := by
  unfold tailWord_4658572
  simp only [CollatzResearch.WordTrace]
  refine ⟨84956039839398369800052985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113274719785864493066737313 84956039839398369800052985)
  ·
    refine ⟨63717029879548777350039739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84956039839398369800052985 63717029879548777350039739)
    ·
      refine ⟨95575544819323166025059609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63717029879548777350039739 95575544819323166025059609)
      ·
        refine ⟨71681658614492374518794707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95575544819323166025059609 71681658614492374518794707)
        ·
          refine ⟨107522487921738561778192061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71681658614492374518794707 107522487921738561778192061)
          ·
            refine ⟨40320932970651960666822023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107522487921738561778192061 40320932970651960666822023)
            ·
              refine ⟨60481399455977941000233035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40320932970651960666822023 60481399455977941000233035)
              ·
                refine ⟨90722099183966911500349553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60481399455977941000233035 90722099183966911500349553)
                ·
                  refine ⟨68041574387975183625262165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90722099183966911500349553 68041574387975183625262165)
                  ·
                    refine ⟨797362199859084183108541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68041574387975183625262165 797362199859084183108541)
                    ·
                      rfl

theorem cell23_4658572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_4658572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658572 prefixEnd_4658572 := by exact prefixLift 4658572
  have htrace : WordTrace (prefixWord ++ tailWord_4658572) baseStart_4658572 baseEnd_4658572 := by
    simpa [prefixWord, tailWord_4658572, baseEnd_4658572] using wordTrace_append hprefix tailTrace_4658572
  have hstable : (prefixWord ++ tailWord_4658572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658572).length < 2 ^ (prefixWord ++ tailWord_4658572).sum := by decide
  have hdescent : baseEnd_4658572 < baseStart_4658572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658656 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 4, 3, 2]
def baseStart_4658656 : Nat := 118140960795 + 4658656 * 2 ^ 59
def prefixEnd_4658656 : Nat := 4983230072969 + 3 ^ 40 * 4658656 * 2
def baseEnd_4658656 : Nat := 2392129731952230220675237

theorem tailTrace_4658656 : CollatzResearch.WordTrace tailWord_4658656 prefixEnd_4658656 2392129731952230220675237 := by
  unfold tailWord_4658656
  simp only [CollatzResearch.WordTrace]
  refine ⟨84957571705246210973081911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113276762273661614630775881 84957571705246210973081911)
  ·
    refine ⟨127436357557869316459622867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84957571705246210973081911 127436357557869316459622867)
    ·
      refine ⟨191154536336803974689434301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127436357557869316459622867 191154536336803974689434301)
      ·
        refine ⟨71682951126301490508537863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191154536336803974689434301 71682951126301490508537863)
        ·
          refine ⟨107524426689452235762806795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71682951126301490508537863 107524426689452235762806795)
          ·
            refine ⟨161286640034178353644210193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107524426689452235762806795 161286640034178353644210193)
            ·
              refine ⟨120964980025633765233157645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161286640034178353644210193 120964980025633765233157645)
              ·
                refine ⟨45361867509612661962434117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120964980025633765233157645 45361867509612661962434117)
                ·
                  refine ⟨8505350158052374117956397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45361867509612661962434117 8505350158052374117956397)
                  ·
                    refine ⟨3189506309269640294233649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8505350158052374117956397 3189506309269640294233649)
                    ·
                      refine ⟨2392129731952230220675237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189506309269640294233649 2392129731952230220675237)
                      ·
                        rfl

theorem cell23_4658656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_4658656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658656 prefixEnd_4658656 := by exact prefixLift 4658656
  have htrace : WordTrace (prefixWord ++ tailWord_4658656) baseStart_4658656 baseEnd_4658656 := by
    simpa [prefixWord, tailWord_4658656, baseEnd_4658656] using wordTrace_append hprefix tailTrace_4658656
  have hstable : (prefixWord ++ tailWord_4658656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658656).length < 2 ^ (prefixWord ++ tailWord_4658656).sum := by decide
  have hdescent : baseEnd_4658656 < baseStart_4658656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658690 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4658690 : Nat := 118140960795 + 4658690 * 2 ^ 59
def prefixEnd_4658690 : Nat := 4983230072969 + 3 ^ 40 * 4658690 * 2
def baseEnd_4658690 : Nat := 2392147190294483087650081

theorem tailTrace_4658690 : CollatzResearch.WordTrace tailWord_4658690 prefixEnd_4658690 2392147190294483087650081 := by
  unfold tailWord_4658690
  simp only [CollatzResearch.WordTrace]
  refine ⟨42479095873092311438225381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113277588994912830501934349 42479095873092311438225381)
  ·
    refine ⟨7964830476204808394667259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42479095873092311438225381 7964830476204808394667259)
    ·
      refine ⟨11947245714307212592000889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7964830476204808394667259 11947245714307212592000889)
      ·
        refine ⟨8960434285730409444000667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11947245714307212592000889 8960434285730409444000667)
        ·
          refine ⟨13440651428595614166001001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8960434285730409444000667 13440651428595614166001001)
          ·
            refine ⟨10080488571446710624500751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13440651428595614166001001 10080488571446710624500751)
            ·
              refine ⟨15120732857170065936751127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10080488571446710624500751 15120732857170065936751127)
              ·
                refine ⟨22681099285755098905126691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15120732857170065936751127 22681099285755098905126691)
                ·
                  refine ⟨34021648928632648357690037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22681099285755098905126691 34021648928632648357690037)
                  ·
                    refine ⟨3189529587059310783533441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34021648928632648357690037 3189529587059310783533441)
                    ·
                      refine ⟨2392147190294483087650081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189529587059310783533441 2392147190294483087650081)
                      ·
                        rfl

theorem cell23_4658690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4658690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658690 prefixEnd_4658690 := by exact prefixLift 4658690
  have htrace : WordTrace (prefixWord ++ tailWord_4658690) baseStart_4658690 baseEnd_4658690 := by
    simpa [prefixWord, tailWord_4658690, baseEnd_4658690] using wordTrace_append hprefix tailTrace_4658690
  have hstable : (prefixWord ++ tailWord_4658690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658690).length < 2 ^ (prefixWord ++ tailWord_4658690).sum := by decide
  have hdescent : baseEnd_4658690 < baseStart_4658690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658700 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_4658700 : Nat := 118140960795 + 4658700 * 2 ^ 59
def prefixEnd_4658700 : Nat := 4983230072969 + 3 ^ 40 * 4658700 * 2
def baseEnd_4658700 : Nat := 797384108367009349508345

theorem tailTrace_4658700 : CollatzResearch.WordTrace tailWord_4658700 prefixEnd_4658700 797384108367009349508345 := by
  unfold tailWord_4658700
  simp only [CollatzResearch.WordTrace]
  refine ⟨84958374111166508730382777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113277832148222011640510369 84958374111166508730382777)
  ·
    refine ⟨63718780583374881547787083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84958374111166508730382777 63718780583374881547787083)
    ·
      refine ⟨95578170875062322321680625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63718780583374881547787083 95578170875062322321680625)
      ·
        refine ⟨71683628156296741741260469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95578170875062322321680625 71683628156296741741260469)
        ·
          refine ⟨6720340139652819538243169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71683628156296741741260469 6720340139652819538243169)
          ·
            refine ⟨5040255104739614653682377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6720340139652819538243169 5040255104739614653682377)
            ·
              refine ⟨3780191328554710990261783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5040255104739614653682377 3780191328554710990261783)
              ·
                refine ⟨5670286992832066485392675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780191328554710990261783 5670286992832066485392675)
                ·
                  refine ⟨8505430489248099728089013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5670286992832066485392675 8505430489248099728089013)
                  ·
                    refine ⟨797384108367009349508345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8505430489248099728089013 797384108367009349508345)
                    ·
                      rfl

theorem cell23_4658700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_4658700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658700 prefixEnd_4658700 := by exact prefixLift 4658700
  have htrace : WordTrace (prefixWord ++ tailWord_4658700) baseStart_4658700 baseEnd_4658700 := by
    simpa [prefixWord, tailWord_4658700, baseEnd_4658700] using wordTrace_append hprefix tailTrace_4658700
  have hstable : (prefixWord ++ tailWord_4658700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658700).length < 2 ^ (prefixWord ++ tailWord_4658700).sum := by decide
  have hdescent : baseEnd_4658700 < baseStart_4658700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658709 : List Nat := [1, 3, 2, 1, 3, 3, 10]
def baseStart_4658709 : Nat := 118140960795 + 4658709 * 2 ^ 59
def prefixEnd_4658709 : Nat := 4983230072969 + 3 ^ 40 * 4658709 * 2
def baseEnd_4658709 : Nat := 29532801807739734732253

theorem tailTrace_4658709 : CollatzResearch.WordTrace tailWord_4658709 prefixEnd_4658709 29532801807739734732253 := by
  unfold tailWord_4658709
  simp only [CollatzResearch.WordTrace]
  refine ⟨169917076479300411997843181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113278050986200274665228787 169917076479300411997843181)
  ·
    refine ⟨63718903679737654499191193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169917076479300411997843181 63718903679737654499191193)
    ·
      refine ⟨47789177759803240874393395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63718903679737654499191193 47789177759803240874393395)
      ·
        refine ⟨71683766639704861311590093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47789177759803240874393395 71683766639704861311590093)
        ·
          refine ⟨26881412489889322991846285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71683766639704861311590093 26881412489889322991846285)
          ·
            refine ⟨10080529683708496121942357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26881412489889322991846285 10080529683708496121942357)
            ·
              refine ⟨29532801807739734732253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10080529683708496121942357 29532801807739734732253)
              ·
                rfl

theorem cell23_4658709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 10].length) (baseStart_4658709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658709 prefixEnd_4658709 := by exact prefixLift 4658709
  have htrace : WordTrace (prefixWord ++ tailWord_4658709) baseStart_4658709 baseEnd_4658709 := by
    simpa [prefixWord, tailWord_4658709, baseEnd_4658709] using wordTrace_append hprefix tailTrace_4658709
  have hstable : (prefixWord ++ tailWord_4658709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658709).length < 2 ^ (prefixWord ++ tailWord_4658709).sum := by decide
  have hdescent : baseEnd_4658709 < baseStart_4658709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658720 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4658720 : Nat := 118140960795 + 4658720 * 2 ^ 59
def prefixEnd_4658720 : Nat := 4983230072969 + 3 ^ 40 * 4658720 * 2
def baseEnd_4658720 : Nat := 2392162594714117970274943

theorem tailTrace_4658720 : CollatzResearch.WordTrace tailWord_4658720 prefixEnd_4658720 2392162594714117970274943 := by
  unfold tailWord_4658720
  simp only [CollatzResearch.WordTrace]
  refine ⟨84958738841130280438246807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113278318454840373917662409 84958738841130280438246807)
  ·
    refine ⟨127438108261695420657370211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84958738841130280438246807 127438108261695420657370211)
    ·
      refine ⟨191157162392543130986055317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127438108261695420657370211 191157162392543130986055317)
      ·
        refine ⟨8960491987150459264971343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191157162392543130986055317 8960491987150459264971343)
        ·
          refine ⟨13440737980725688897457015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8960491987150459264971343 13440737980725688897457015)
          ·
            refine ⟨20161106971088533346185523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13440737980725688897457015 20161106971088533346185523)
            ·
              refine ⟨30241660456632800019278285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20161106971088533346185523 30241660456632800019278285)
              ·
                refine ⟨11340622671237300007229357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30241660456632800019278285 11340622671237300007229357)
                ·
                  refine ⟨4252733501713987502711009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11340622671237300007229357 4252733501713987502711009)
                  ·
                    refine ⟨3189550126285490627033257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4252733501713987502711009 3189550126285490627033257)
                    ·
                      refine ⟨2392162594714117970274943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189550126285490627033257 2392162594714117970274943)
                      ·
                        rfl

theorem cell23_4658720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4658720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658720 prefixEnd_4658720 := by exact prefixLift 4658720
  have htrace : WordTrace (prefixWord ++ tailWord_4658720) baseStart_4658720 baseEnd_4658720 := by
    simpa [prefixWord, tailWord_4658720, baseEnd_4658720] using wordTrace_append hprefix tailTrace_4658720
  have hstable : (prefixWord ++ tailWord_4658720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658720).length < 2 ^ (prefixWord ++ tailWord_4658720).sum := by decide
  have hdescent : baseEnd_4658720 < baseStart_4658720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658730 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_4658730 : Nat := 118140960795 + 4658730 * 2 ^ 59
def prefixEnd_4658730 : Nat := 4983230072969 + 3 ^ 40 * 4658730 * 2
def baseEnd_4658730 : Nat := 797389243173554310383299

theorem tailTrace_4658730 : CollatzResearch.WordTrace tailWord_4658730 prefixEnd_4658730 797389243173554310383299 := by
  unfold tailWord_4658730
  simp only [CollatzResearch.WordTrace]
  refine ⟨42479460603056083146089411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113278561608149555056238429 42479460603056083146089411)
  ·
    refine ⟨63719190904584124719134117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42479460603056083146089411 63719190904584124719134117)
    ·
      refine ⟨11947348294609523384837647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63719190904584124719134117 11947348294609523384837647)
      ·
        refine ⟨17921022441914285077256471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947348294609523384837647 17921022441914285077256471)
        ·
          refine ⟨26881533662871427615884707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17921022441914285077256471 26881533662871427615884707)
          ·
            refine ⟨40322300494307141423827061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26881533662871427615884707 40322300494307141423827061)
            ·
              refine ⟨3780215671341294508483787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40322300494307141423827061 3780215671341294508483787)
              ·
                refine ⟨5670323507011941762725681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780215671341294508483787 5670323507011941762725681)
                ·
                  refine ⟨4252742630258956322044261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5670323507011941762725681 4252742630258956322044261)
                  ·
                    refine ⟨797389243173554310383299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4252742630258956322044261 797389243173554310383299)
                    ·
                      rfl

theorem cell23_4658730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_4658730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658730 prefixEnd_4658730 := by exact prefixLift 4658730
  have htrace : WordTrace (prefixWord ++ tailWord_4658730) baseStart_4658730 baseEnd_4658730 := by
    simpa [prefixWord, tailWord_4658730, baseEnd_4658730] using wordTrace_append hprefix tailTrace_4658730
  have hstable : (prefixWord ++ tailWord_4658730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658730).length < 2 ^ (prefixWord ++ tailWord_4658730).sum := by decide
  have hdescent : baseEnd_4658730 < baseStart_4658730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658753 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4658753 : Nat := 118140960795 + 4658753 * 2 ^ 59
def prefixEnd_4658753 : Nat := 4983230072969 + 3 ^ 40 * 4658753 * 2
def baseEnd_4658753 : Nat := 2392179539575716341162291

theorem tailTrace_4658753 : CollatzResearch.WordTrace tailWord_4658753 prefixEnd_4658753 2392179539575716341162291 := by
  unfold tailWord_4658753
  simp only [CollatzResearch.WordTrace]
  refine ⟨169918681291141007512444913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113279120860760671674963275 169918681291141007512444913)
  ·
    refine ⟨127439010968355755634333685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169918681291141007512444913 127439010968355755634333685)
    ·
      refine ⟨11947407278283352090718783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127439010968355755634333685 11947407278283352090718783)
      ·
        refine ⟨17921110917425028136078175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947407278283352090718783 17921110917425028136078175)
        ·
          refine ⟨26881666376137542204117263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17921110917425028136078175 26881666376137542204117263)
          ·
            refine ⟨40322499564206313306175895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26881666376137542204117263 40322499564206313306175895)
            ·
              refine ⟨60483749346309469959263843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40322499564206313306175895 60483749346309469959263843)
              ·
                refine ⟨90725624019464204938895765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60483749346309469959263843 90725624019464204938895765)
                ·
                  refine ⟨4252763625912384606510739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90725624019464204938895765 4252763625912384606510739)
                  ·
                    refine ⟨6379145438868576909766109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4252763625912384606510739 6379145438868576909766109)
                    ·
                      refine ⟨2392179539575716341162291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379145438868576909766109 2392179539575716341162291)
                      ·
                        rfl

theorem cell23_4658753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4658753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658753 prefixEnd_4658753 := by exact prefixLift 4658753
  have htrace : WordTrace (prefixWord ++ tailWord_4658753) baseStart_4658753 baseEnd_4658753 := by
    simpa [prefixWord, tailWord_4658753, baseEnd_4658753] using wordTrace_append hprefix tailTrace_4658753
  have hstable : (prefixWord ++ tailWord_4658753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658753).length < 2 ^ (prefixWord ++ tailWord_4658753).sum := by decide
  have hdescent : baseEnd_4658753 < baseStart_4658753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658781 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4658781 : Nat := 118140960795 + 4658781 * 2 ^ 59
def prefixEnd_4658781 : Nat := 4983230072969 + 3 ^ 40 * 4658781 * 2
def baseEnd_4658781 : Nat := 797397972344680743870721

theorem tailTrace_4658781 : CollatzResearch.WordTrace tailWord_4658781 prefixEnd_4658781 797397972344680743870721 := by
  unfold tailWord_4658781
  simp only [CollatzResearch.WordTrace]
  refine ⟨169919702535039568294464197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113279801690026378862976131 169919702535039568294464197)
  ·
    refine ⟨31859944225319919055212037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169919702535039568294464197 31859944225319919055212037)
    ·
      refine ⟨5973739542247484822852257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31859944225319919055212037 5973739542247484822852257)
      ·
        refine ⟨4480304656685613617139193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5973739542247484822852257 4480304656685613617139193)
        ·
          refine ⟨3360228492514210212854395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4480304656685613617139193 3360228492514210212854395)
          ·
            refine ⟨5040342738771315319281593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360228492514210212854395 5040342738771315319281593)
            ·
              refine ⟨3780257054078486489461195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5040342738771315319281593 3780257054078486489461195)
              ·
                refine ⟨5670385581117729734191793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780257054078486489461195 5670385581117729734191793)
                ·
                  refine ⟨4252789185838297300643845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5670385581117729734191793 4252789185838297300643845)
                  ·
                    refine ⟨797397972344680743870721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4252789185838297300643845 797397972344680743870721)
                    ·
                      rfl

theorem cell23_4658781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4658781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658781 prefixEnd_4658781 := by exact prefixLift 4658781
  have htrace : WordTrace (prefixWord ++ tailWord_4658781) baseStart_4658781 baseEnd_4658781 := by
    simpa [prefixWord, tailWord_4658781, baseEnd_4658781] using wordTrace_append hprefix tailTrace_4658781
  have hstable : (prefixWord ++ tailWord_4658781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658781).length < 2 ^ (prefixWord ++ tailWord_4658781).sum := by decide
  have hdescent : baseEnd_4658781 < baseStart_4658781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658787 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 2, 1, 3]
def baseStart_4658787 : Nat := 118140960795 + 4658787 * 2 ^ 59
def prefixEnd_4658787 : Nat := 4983230072969 + 3 ^ 40 * 4658787 * 2
def baseEnd_4658787 : Nat := 2392196997917969208137135

theorem tailTrace_4658787 : CollatzResearch.WordTrace tailWord_4658787 prefixEnd_4658787 2392196997917969208137135 := by
  unfold tailWord_4658787
  simp only [CollatzResearch.WordTrace]
  refine ⟨169919921373017831319182615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113279947582011887546121743 169919921373017831319182615)
  ·
    refine ⟨254879882059526746978773923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169919921373017831319182615 254879882059526746978773923)
    ·
      refine ⟨382319823089290120468160885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254879882059526746978773923 382319823089290120468160885)
      ·
        refine ⟨35842483414620948793890083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 382319823089290120468160885 35842483414620948793890083)
        ·
          refine ⟨53763725121931423190835125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35842483414620948793890083 53763725121931423190835125)
          ·
            refine ⟨5040349230181070924140793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53763725121931423190835125 5040349230181070924140793)
            ·
              refine ⟨3780261922635803193105595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5040349230181070924140793 3780261922635803193105595)
              ·
                refine ⟨5670392883953704789658393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780261922635803193105595 5670392883953704789658393)
                ·
                  refine ⟨4252794662965278592243795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5670392883953704789658393 4252794662965278592243795)
                  ·
                    refine ⟨6379191994447917888365693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4252794662965278592243795 6379191994447917888365693)
                    ·
                      refine ⟨2392196997917969208137135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379191994447917888365693 2392196997917969208137135)
                      ·
                        rfl

theorem cell23_4658787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_4658787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658787 prefixEnd_4658787 := by exact prefixLift 4658787
  have htrace : WordTrace (prefixWord ++ tailWord_4658787) baseStart_4658787 baseEnd_4658787 := by
    simpa [prefixWord, tailWord_4658787, baseEnd_4658787] using wordTrace_append hprefix tailTrace_4658787
  have hstable : (prefixWord ++ tailWord_4658787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658787).length < 2 ^ (prefixWord ++ tailWord_4658787).sum := by decide
  have hdescent : baseEnd_4658787 < baseStart_4658787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658799 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 9]
def baseStart_4658799 : Nat := 118140960795 + 4658799 * 2 ^ 59
def prefixEnd_4658799 : Nat := 4983230072969 + 3 ^ 40 * 4658799 * 2
def baseEnd_4658799 : Nat := 265800351076202573465231

theorem tailTrace_4658799 : CollatzResearch.WordTrace tailWord_4658799 prefixEnd_4658799 265800351076202573465231 := by
  unfold tailWord_4658799
  simp only [CollatzResearch.WordTrace]
  refine ⟨169920359048974357368619451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113280239365982904912412967 169920359048974357368619451)
  ·
    refine ⟨254880538573461536052929177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169920359048974357368619451 254880538573461536052929177)
    ·
      refine ⟨191160403930096152039696883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254880538573461536052929177 191160403930096152039696883)
      ·
        refine ⟨286740605895144228059545325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191160403930096152039696883 286740605895144228059545325)
        ·
          refine ⟨107527727210679085522329497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286740605895144228059545325 107527727210679085522329497)
          ·
            refine ⟨80645795408009314141747123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107527727210679085522329497 80645795408009314141747123)
            ·
              refine ⟨120968693112013971212620685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80645795408009314141747123 120968693112013971212620685)
              ·
                refine ⟨45363259917005239204732757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120968693112013971212620685 45363259917005239204732757)
                ·
                  refine ⟨265800351076202573465231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45363259917005239204732757 265800351076202573465231)
                  ·
                    rfl

theorem cell23_4658799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 9].length) (baseStart_4658799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658799 prefixEnd_4658799 := by exact prefixLift 4658799
  have htrace : WordTrace (prefixWord ++ tailWord_4658799) baseStart_4658799 baseEnd_4658799 := by
    simpa [prefixWord, tailWord_4658799, baseEnd_4658799] using wordTrace_append hprefix tailTrace_4658799
  have hstable : (prefixWord ++ tailWord_4658799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658799).length < 2 ^ (prefixWord ++ tailWord_4658799).sum := by decide
  have hdescent : baseEnd_4658799 < baseStart_4658799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658850 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_4658850 : Nat := 118140960795 + 4658850 * 2 ^ 59
def prefixEnd_4658850 : Nat := 4983230072969 + 3 ^ 40 * 4658850 * 2
def baseEnd_4658850 : Nat := 265803260799911384627705

theorem tailTrace_4658850 : CollatzResearch.WordTrace tailWord_4658850 prefixEnd_4658850 265803260799911384627705 := by
  unfold tailWord_4658850
  simp only [CollatzResearch.WordTrace]
  refine ⟨42480554792947398269681501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113281479447859728719150669 42480554792947398269681501)
  ·
    refine ⟨15930208047355274351130563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42480554792947398269681501 15930208047355274351130563)
    ·
      refine ⟨23895312071032911526695845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15930208047355274351130563 23895312071032911526695845)
      ·
        refine ⟨4480371013318670911255471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23895312071032911526695845 4480371013318670911255471)
        ·
          refine ⟨6720556519978006366883207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480371013318670911255471 6720556519978006366883207)
          ·
            refine ⟨10080834779967009550324811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6720556519978006366883207 10080834779967009550324811)
            ·
              refine ⟨15121252169950514325487217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10080834779967009550324811 15121252169950514325487217)
              ·
                refine ⟨11340939127462885744115413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15121252169950514325487217 11340939127462885744115413)
                ·
                  refine ⟨265803260799911384627705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11340939127462885744115413 265803260799911384627705)
                  ·
                    rfl

theorem cell23_4658850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_4658850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658850 prefixEnd_4658850 := by exact prefixLift 4658850
  have htrace : WordTrace (prefixWord ++ tailWord_4658850) baseStart_4658850 baseEnd_4658850 := by
    simpa [prefixWord, tailWord_4658850, baseEnd_4658850] using wordTrace_append hprefix tailTrace_4658850
  have hstable : (prefixWord ++ tailWord_4658850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658850).length < 2 ^ (prefixWord ++ tailWord_4658850).sum := by decide
  have hdescent : baseEnd_4658850 < baseStart_4658850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658970 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_4658970 : Nat := 118140960795 + 4658970 * 2 ^ 59
def prefixEnd_4658970 : Nat := 4983230072969 + 3 ^ 40 * 4658970 * 2
def baseEnd_4658970 : Nat := 797430321625913997382931

theorem tailTrace_4658970 : CollatzResearch.WordTrace tailWord_4658970 prefixEnd_4658970 797430321625913997382931 := by
  unfold tailWord_4658970
  simp only [CollatzResearch.WordTrace]
  refine ⟨42481648982838713393273591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113284397287569902382062909 42481648982838713393273591)
  ·
    refine ⟨63722473474258070089910387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42481648982838713393273591 63722473474258070089910387)
    ·
      refine ⟨95583710211387105134865581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63722473474258070089910387 95583710211387105134865581)
      ·
        refine ⟨35843891329270164425574593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95583710211387105134865581 35843891329270164425574593)
        ·
          refine ⟨26882918496952623319180945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35843891329270164425574593 26882918496952623319180945)
          ·
            refine ⟨20162188872714467489385709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26882918496952623319180945 20162188872714467489385709)
            ·
              refine ⟨7560820827267925308519641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20162188872714467489385709 7560820827267925308519641)
              ·
                refine ⟨5670615620450943981389731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7560820827267925308519641 5670615620450943981389731)
                ·
                  refine ⟨8505923430676415972084597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5670615620450943981389731 8505923430676415972084597)
                  ·
                    refine ⟨797430321625913997382931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8505923430676415972084597 797430321625913997382931)
                    ·
                      rfl

theorem cell23_4658970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_4658970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658970 prefixEnd_4658970 := by exact prefixLift 4658970
  have htrace : WordTrace (prefixWord ++ tailWord_4658970) baseStart_4658970 baseEnd_4658970 := by
    simpa [prefixWord, tailWord_4658970, baseEnd_4658970] using wordTrace_append hprefix tailTrace_4658970
  have hstable : (prefixWord ++ tailWord_4658970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658970).length < 2 ^ (prefixWord ++ tailWord_4658970).sum := by decide
  have hdescent : baseEnd_4658970 < baseStart_4658970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658977 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4658977 : Nat := 118140960795 + 4658977 * 2 ^ 59
def prefixEnd_4658977 : Nat := 4983230072969 + 3 ^ 40 * 4658977 * 2
def baseEnd_4658977 : Nat := 2392294559242323464761261

theorem tailTrace_4658977 : CollatzResearch.WordTrace tailWord_4658977 prefixEnd_4658977 2392294559242323464761261 := by
  unfold tailWord_4658977
  simp only [CollatzResearch.WordTrace]
  refine ⟨169926851242329493768599185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113284567494886329179066123 169926851242329493768599185)
  ·
    refine ⟨127445138431747120326449389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169926851242329493768599185 127445138431747120326449389)
    ·
      refine ⟨47791926911905170122418521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127445138431747120326449389 47791926911905170122418521)
      ·
        refine ⟨35843945183928877591813891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47791926911905170122418521 35843945183928877591813891)
        ·
          refine ⟨53765917775893316387720837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35843945183928877591813891 53765917775893316387720837)
          ·
            refine ⟨10081109582979996822697657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53765917775893316387720837 10081109582979996822697657)
            ·
              refine ⟨7560832187234997617023243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10081109582979996822697657 7560832187234997617023243)
              ·
                refine ⟨11341248280852496425534865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7560832187234997617023243 11341248280852496425534865)
                ·
                  refine ⟨8505936210639372319151149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11341248280852496425534865 8505936210639372319151149)
                  ·
                    refine ⟨3189726078989764619681681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8505936210639372319151149 3189726078989764619681681)
                    ·
                      refine ⟨2392294559242323464761261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189726078989764619681681 2392294559242323464761261)
                      ·
                        rfl

theorem cell23_4658977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4658977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4658977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4658977 prefixEnd_4658977 := by exact prefixLift 4658977
  have htrace : WordTrace (prefixWord ++ tailWord_4658977) baseStart_4658977 baseEnd_4658977 := by
    simpa [prefixWord, tailWord_4658977, baseEnd_4658977] using wordTrace_append hprefix tailTrace_4658977
  have hstable : (prefixWord ++ tailWord_4658977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658977).length < 2 ^ (prefixWord ++ tailWord_4658977).sum := by decide
  have hdescent : baseEnd_4658977 < baseStart_4658977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659000 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 2, 4]
def baseStart_4659000 : Nat := 118140960795 + 4659000 * 2 ^ 59
def prefixEnd_4659000 : Nat := 4983230072969 + 3 ^ 40 * 4659000 * 2
def baseEnd_4659000 : Nat := 797435456432458958257885

theorem tailTrace_4659000 : CollatzResearch.WordTrace tailWord_4659000 prefixEnd_4659000 797435456432458958257885 := by
  unfold tailWord_4659000
  simp only [CollatzResearch.WordTrace]
  refine ⟨84963845060623084348343227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113285126747497445797790969 84963845060623084348343227)
  ·
    refine ⟨127445767590934626522514841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84963845060623084348343227 127445767590934626522514841)
    ·
      refine ⟨95584325693200969891886131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127445767590934626522514841 95584325693200969891886131)
      ·
        refine ⟨143376488539801454837829197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95584325693200969891886131 143376488539801454837829197)
        ·
          refine ⟨53766183202425545564185949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143376488539801454837829197 53766183202425545564185949)
          ·
            refine ⟨20162318700909579586569731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53766183202425545564185949 20162318700909579586569731)
            ·
              refine ⟨30243478051364369379854597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20162318700909579586569731 30243478051364369379854597)
              ·
                refine ⟨5670652134630819258722737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30243478051364369379854597 5670652134630819258722737)
                ·
                  refine ⟨4252989100973114444042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5670652134630819258722737 4252989100973114444042053)
                  ·
                    refine ⟨797435456432458958257885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4252989100973114444042053 797435456432458958257885)
                    ·
                      rfl

theorem cell23_4659000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_4659000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659000 prefixEnd_4659000 := by exact prefixLift 4659000
  have htrace : WordTrace (prefixWord ++ tailWord_4659000) baseStart_4659000 baseEnd_4659000 := by
    simpa [prefixWord, tailWord_4659000, baseEnd_4659000] using wordTrace_append hprefix tailTrace_4659000
  have hstable : (prefixWord ++ tailWord_4659000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659000).length < 2 ^ (prefixWord ++ tailWord_4659000).sum := by decide
  have hdescent : baseEnd_4659000 < baseStart_4659000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659001 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4659001 : Nat := 118140960795 + 4659001 * 2 ^ 59
def prefixEnd_4659001 : Nat := 4983230072969 + 3 ^ 40 * 4659001 * 2
def baseEnd_4659001 : Nat := 2392306882778031370861151

theorem tailTrace_4659001 : CollatzResearch.WordTrace tailWord_4659001 prefixEnd_4659001 2392306882778031370861151 := by
  unfold tailWord_4659001
  simp only [CollatzResearch.WordTrace]
  refine ⟨169927726594242545867472857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113285151062828363911648571 169927726594242545867472857)
  ·
    refine ⟨127445794945681909400604643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169927726594242545867472857 127445794945681909400604643)
    ·
      refine ⟨191168692418522864100906965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127445794945681909400604643 191168692418522864100906965)
      ·
        refine ⟨4480516228559129627365007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 191168692418522864100906965 4480516228559129627365007)
        ·
          refine ⟨6720774342838694441047511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480516228559129627365007 6720774342838694441047511)
          ·
            refine ⟨10081161514258041661571267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6720774342838694441047511 10081161514258041661571267)
            ·
              refine ⟨15121742271387062492356901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10081161514258041661571267 15121742271387062492356901)
              ·
                refine ⟨2835326675885074217316919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15121742271387062492356901 2835326675885074217316919)
                ·
                  refine ⟨4252990013827611325975379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835326675885074217316919 4252990013827611325975379)
                  ·
                    refine ⟨6379485020741416988963069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4252990013827611325975379 6379485020741416988963069)
                    ·
                      refine ⟨2392306882778031370861151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379485020741416988963069 2392306882778031370861151)
                      ·
                        rfl

theorem cell23_4659001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4659001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659001 prefixEnd_4659001 := by exact prefixLift 4659001
  have htrace : WordTrace (prefixWord ++ tailWord_4659001) baseStart_4659001 baseEnd_4659001 := by
    simpa [prefixWord, tailWord_4659001, baseEnd_4659001] using wordTrace_append hprefix tailTrace_4659001
  have hstable : (prefixWord ++ tailWord_4659001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659001).length < 2 ^ (prefixWord ++ tailWord_4659001).sum := by decide
  have hdescent : baseEnd_4659001 < baseStart_4659001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659040 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_4659040 : Nat := 118140960795 + 4659040 * 2 ^ 59
def prefixEnd_4659040 : Nat := 4983230072969 + 3 ^ 40 * 4659040 * 2
def baseEnd_4659040 : Nat := 2392326908523556718273471

theorem tailTrace_4659040 : CollatzResearch.WordTrace tailWord_4659040 prefixEnd_4659040 2392326908523556718273471 := by
  unfold tailWord_4659040
  simp only [CollatzResearch.WordTrace]
  refine ⟨84964574520550627764071287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113286099360734170352095049 84964574520550627764071287)
  ·
    refine ⟨127446861780825941646106931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84964574520550627764071287 127446861780825941646106931)
    ·
      refine ⟨191170292671238912469160397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127446861780825941646106931 191170292671238912469160397)
      ·
        refine ⟨71688859751714592175935149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191170292671238912469160397 71688859751714592175935149)
        ·
          refine ⟨26883322406892972065975681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71688859751714592175935149 26883322406892972065975681)
          ·
            refine ⟨20162491805169729049481761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26883322406892972065975681 20162491805169729049481761)
            ·
              refine ⟨15121868853877296787111321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20162491805169729049481761 15121868853877296787111321)
              ·
                refine ⟨11341401640407972590333491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15121868853877296787111321 11341401640407972590333491)
                ·
                  refine ⟨17012102460611958885500237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11341401640407972590333491 17012102460611958885500237)
                  ·
                    refine ⟨6379538422729484582062589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17012102460611958885500237 6379538422729484582062589)
                    ·
                      refine ⟨2392326908523556718273471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379538422729484582062589 2392326908523556718273471)
                      ·
                        rfl

theorem cell23_4659040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_4659040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659040 prefixEnd_4659040 := by exact prefixLift 4659040
  have htrace : WordTrace (prefixWord ++ tailWord_4659040) baseStart_4659040 baseEnd_4659040 := by
    simpa [prefixWord, tailWord_4659040, baseEnd_4659040] using wordTrace_append hprefix tailTrace_4659040
  have hstable : (prefixWord ++ tailWord_4659040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659040).length < 2 ^ (prefixWord ++ tailWord_4659040).sum := by decide
  have hdescent : baseEnd_4659040 < baseStart_4659040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659083 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5]
def baseStart_4659083 : Nat := 118140960795 + 4659083 * 2 ^ 59
def prefixEnd_4659083 : Nat := 4983230072969 + 3 ^ 40 * 4659083 * 2
def baseEnd_4659083 : Nat := 2392348988191700050035773

theorem tailTrace_4659083 : CollatzResearch.WordTrace tailWord_4659083 prefixEnd_4659083 2392348988191700050035773 := by
  unfold tailWord_4659083
  simp only [CollatzResearch.WordTrace]
  refine ⟨169930717379945473871957903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113287144919963649247971935 169930717379945473871957903)
  ·
    refine ⟨254896076069918210807936855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169930717379945473871957903 254896076069918210807936855)
    ·
      refine ⟨382344114104877316211905283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254896076069918210807936855 382344114104877316211905283)
      ·
        refine ⟨573516171157315974317857925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382344114104877316211905283 573516171157315974317857925)
        ·
          refine ⟨107534282091996745184598361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 573516171157315974317857925 107534282091996745184598361)
          ·
            refine ⟨80650711568997558888448771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107534282091996745184598361 80650711568997558888448771)
            ·
              refine ⟨120976067353496338332673157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80650711568997558888448771 120976067353496338332673157)
              ·
                refine ⟨22683012628780563437376217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120976067353496338332673157 22683012628780563437376217)
                ·
                  refine ⟨17012259471585422578032163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22683012628780563437376217 17012259471585422578032163)
                  ·
                    refine ⟨25518389207378133867048245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17012259471585422578032163 25518389207378133867048245)
                    ·
                      refine ⟨2392348988191700050035773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25518389207378133867048245 2392348988191700050035773)
                      ·
                        rfl

theorem cell23_4659083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_4659083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659083 prefixEnd_4659083 := by exact prefixLift 4659083
  have htrace : WordTrace (prefixWord ++ tailWord_4659083) baseStart_4659083 baseEnd_4659083 := by
    simpa [prefixWord, tailWord_4659083, baseEnd_4659083] using wordTrace_append hprefix tailTrace_4659083
  have hstable : (prefixWord ++ tailWord_4659083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659083).length < 2 ^ (prefixWord ++ tailWord_4659083).sum := by decide
  have hdescent : baseEnd_4659083 < baseStart_4659083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659097 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 4, 2, 2]
def baseStart_4659097 : Nat := 118140960795 + 4659097 * 2 ^ 59
def prefixEnd_4659097 : Nat := 4983230072969 + 3 ^ 40 * 4659097 * 2
def baseEnd_4659097 : Nat := 2392356176920862995260709

theorem tailTrace_4659097 : CollatzResearch.WordTrace tailWord_4659097 prefixEnd_4659097 2392356176920862995260709 := by
  unfold tailWord_4659097
  simp only [CollatzResearch.WordTrace]
  refine ⟨169931228001894754262967545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113287485334596502841978363 169931228001894754262967545)
  ·
    refine ⟨127448421001421065697225659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169931228001894754262967545 127448421001421065697225659)
    ·
      refine ⟨191172631502131598545838489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127448421001421065697225659 191172631502131598545838489)
      ·
        refine ⟨143379473626598698909378867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191172631502131598545838489 143379473626598698909378867)
        ·
          refine ⟨215069210439898048364068301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143379473626598698909378867 215069210439898048364068301)
          ·
            refine ⟨80650953914961768136525613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215069210439898048364068301 80650953914961768136525613)
            ·
              refine ⟨30244107718110663051197105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80650953914961768136525613 30244107718110663051197105)
              ·
                refine ⟨22683080788582997288397829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30244107718110663051197105 22683080788582997288397829)
                ·
                  refine ⟨4253077647859311991574593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22683080788582997288397829 4253077647859311991574593)
                  ·
                    refine ⟨3189808235894483993680945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4253077647859311991574593 3189808235894483993680945)
                    ·
                      refine ⟨2392356176920862995260709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189808235894483993680945 2392356176920862995260709)
                      ·
                        rfl

theorem cell23_4659097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_4659097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659097 prefixEnd_4659097 := by exact prefixLift 4659097
  have htrace : WordTrace (prefixWord ++ tailWord_4659097) baseStart_4659097 baseEnd_4659097 := by
    simpa [prefixWord, tailWord_4659097, baseEnd_4659097] using wordTrace_append hprefix tailTrace_4659097
  have hstable : (prefixWord ++ tailWord_4659097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659097).length < 2 ^ (prefixWord ++ tailWord_4659097).sum := by decide
  have hdescent : baseEnd_4659097 < baseStart_4659097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659100 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4659100 : Nat := 118140960795 + 4659100 * 2 ^ 59
def prefixEnd_4659100 : Nat := 4983230072969 + 3 ^ 40 * 4659100 * 2
def baseEnd_4659100 : Nat := 2392357717362826483523195

theorem tailTrace_4659100 : CollatzResearch.WordTrace tailWord_4659100 prefixEnd_4659100 2392357717362826483523195 := by
  unfold tailWord_4659100
  simp only [CollatzResearch.WordTrace]
  refine ⟨84965668710441942887663377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113287558280589257183551169 84965668710441942887663377)
  ·
    refine ⟨63724251532831457165747533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84965668710441942887663377 63724251532831457165747533)
    ·
      refine ⟨23896594324811796437155325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63724251532831457165747533 23896594324811796437155325)
      ·
        refine ⟨8961222871804423663933247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23896594324811796437155325 8961222871804423663933247)
        ·
          refine ⟨13441834307706635495899871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8961222871804423663933247 13441834307706635495899871)
          ·
            refine ⟨20162751461559953243849807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13441834307706635495899871 20162751461559953243849807)
            ·
              refine ⟨30244127192339929865774711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20162751461559953243849807 30244127192339929865774711)
              ·
                refine ⟨45366190788509894798662067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30244127192339929865774711 45366190788509894798662067)
                ·
                  refine ⟨68049286182764842197993101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45366190788509894798662067 68049286182764842197993101)
                  ·
                    refine ⟨25518482318536815824247413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68049286182764842197993101 25518482318536815824247413)
                    ·
                      refine ⟨2392357717362826483523195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25518482318536815824247413 2392357717362826483523195)
                      ·
                        rfl

theorem cell23_4659100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4659100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659100 prefixEnd_4659100 := by exact prefixLift 4659100
  have htrace : WordTrace (prefixWord ++ tailWord_4659100) baseStart_4659100 baseEnd_4659100 := by
    simpa [prefixWord, tailWord_4659100, baseEnd_4659100] using wordTrace_append hprefix tailTrace_4659100
  have hstable : (prefixWord ++ tailWord_4659100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659100).length < 2 ^ (prefixWord ++ tailWord_4659100).sum := by decide
  have hdescent : baseEnd_4659100 < baseStart_4659100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659143 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_4659143 : Nat := 118140960795 + 4659143 * 2 ^ 59
def prefixEnd_4659143 : Nat := 4983230072969 + 3 ^ 40 * 4659143 * 2
def baseEnd_4659143 : Nat := 2392379797030969815285497

theorem tailTrace_4659143 : CollatzResearch.WordTrace tailWord_4659143 prefixEnd_4659143 2392379797030969815285497 := by
  unfold tailWord_4659143
  simp only [CollatzResearch.WordTrace]
  refine ⟨169932905759728104119142083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113288603839818736079428055 169932905759728104119142083)
  ·
    refine ⟨254899358639592156178713125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169932905759728104119142083 254899358639592156178713125)
    ·
      refine ⟨47793629744923529283508711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254899358639592156178713125 47793629744923529283508711)
      ·
        refine ⟨71690444617385293925263067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47793629744923529283508711 71690444617385293925263067)
        ·
          refine ⟨107535666926077940887894601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71690444617385293925263067 107535666926077940887894601)
          ·
            refine ⟨80651750194558455665920951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107535666926077940887894601 80651750194558455665920951)
            ·
              refine ⟨120977625291837683498881427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80651750194558455665920951 120977625291837683498881427)
              ·
                refine ⟨181466437937756525248322141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120977625291837683498881427 181466437937756525248322141)
                ·
                  refine ⟨68049914226658696968120803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181466437937756525248322141 68049914226658696968120803)
                  ·
                    refine ⟨102074871339988045452181205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68049914226658696968120803 102074871339988045452181205)
                    ·
                      refine ⟨2392379797030969815285497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102074871339988045452181205 2392379797030969815285497)
                      ·
                        rfl

theorem cell23_4659143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_4659143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659143 prefixEnd_4659143 := by exact prefixLift 4659143
  have htrace : WordTrace (prefixWord ++ tailWord_4659143) baseStart_4659143 baseEnd_4659143 := by
    simpa [prefixWord, tailWord_4659143, baseEnd_4659143] using wordTrace_append hprefix tailTrace_4659143
  have hstable : (prefixWord ++ tailWord_4659143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659143).length < 2 ^ (prefixWord ++ tailWord_4659143).sum := by decide
  have hdescent : baseEnd_4659143 < baseStart_4659143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659180 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_4659180 : Nat := 118140960795 + 4659180 * 2 ^ 59
def prefixEnd_4659180 : Nat := 4983230072969 + 3 ^ 40 * 4659180 * 2
def baseEnd_4659180 : Nat := 797466265271728723507609

theorem tailTrace_4659180 : CollatzResearch.WordTrace tailWord_4659180 prefixEnd_4659180 797466265271728723507609 := by
  unfold tailWord_4659180
  simp only [CollatzResearch.WordTrace]
  refine ⟨84967127630297029719119497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113289503507062706292159329 84967127630297029719119497)
  ·
    refine ⟨63725345722722772289339623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84967127630297029719119497 63725345722722772289339623)
    ·
      refine ⟨95588018584084158434009435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63725345722722772289339623 95588018584084158434009435)
      ·
        refine ⟨143382027876126237651014153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95588018584084158434009435 143382027876126237651014153)
        ·
          refine ⟨107536520907094678238260615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143382027876126237651014153 107536520907094678238260615)
          ·
            refine ⟨161304781360642017357390923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107536520907094678238260615 161304781360642017357390923)
            ·
              refine ⟨241957172040963026036086385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161304781360642017357390923 241957172040963026036086385)
              ·
                refine ⟨181467879030722269527064789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241957172040963026036086385 181467879030722269527064789)
                ·
                  refine ⟨4253153414782553192040581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 181467879030722269527064789 4253153414782553192040581)
                  ·
                    refine ⟨797466265271728723507609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4253153414782553192040581 797466265271728723507609)
                    ·
                      rfl

theorem cell23_4659180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_4659180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659180 prefixEnd_4659180 := by exact prefixLift 4659180
  have htrace : WordTrace (prefixWord ++ tailWord_4659180) baseStart_4659180 baseEnd_4659180 := by
    simpa [prefixWord, tailWord_4659180, baseEnd_4659180] using wordTrace_append hprefix tailTrace_4659180
  have hstable : (prefixWord ++ tailWord_4659180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659180).length < 2 ^ (prefixWord ++ tailWord_4659180).sum := by decide
  have hdescent : baseEnd_4659180 < baseStart_4659180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659204 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4659204 : Nat := 118140960795 + 4659204 * 2 ^ 59
def prefixEnd_4659204 : Nat := 4983230072969 + 3 ^ 40 * 4659204 * 2
def baseEnd_4659204 : Nat := 2392411119350894076622717

theorem tailTrace_4659204 : CollatzResearch.WordTrace tailWord_4659204 prefixEnd_4659204 2392411119350894076622717 := by
  unfold tailWord_4659204
  simp only [CollatzResearch.WordTrace]
  refine ⟨84967565306253555768556333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113290087075004741024741777 84967565306253555768556333)
  ·
    refine ⟨31862836989845083413208625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84967565306253555768556333 31862836989845083413208625)
    ·
      refine ⟨23897127742383812559906469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31862836989845083413208625 23897127742383812559906469)
      ·
        refine ⟨4480711451696964854982463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23897127742383812559906469 4480711451696964854982463)
        ·
          refine ⟨6721067177545447282473695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480711451696964854982463 6721067177545447282473695)
          ·
            refine ⟨10081600766318170923710543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721067177545447282473695 10081600766318170923710543)
            ·
              refine ⟨15122401149477256385565815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10081600766318170923710543 15122401149477256385565815)
              ·
                refine ⟨22683601724215884578348723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15122401149477256385565815 22683601724215884578348723)
                ·
                  refine ⟨34025402586323826867523085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22683601724215884578348723 34025402586323826867523085)
                  ·
                    refine ⟨12759525969871435075321157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34025402586323826867523085 12759525969871435075321157)
                    ·
                      refine ⟨2392411119350894076622717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12759525969871435075321157 2392411119350894076622717)
                      ·
                        rfl

theorem cell23_4659204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4659204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659204 prefixEnd_4659204 := by exact prefixLift 4659204
  have htrace : WordTrace (prefixWord ++ tailWord_4659204) baseStart_4659204 baseEnd_4659204 := by
    simpa [prefixWord, tailWord_4659204, baseEnd_4659204] using wordTrace_append hprefix tailTrace_4659204
  have hstable : (prefixWord ++ tailWord_4659204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659204).length < 2 ^ (prefixWord ++ tailWord_4659204).sum := by decide
  have hdescent : baseEnd_4659204 < baseStart_4659204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659207 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4659207 : Nat := 118140960795 + 4659207 * 2 ^ 59
def prefixEnd_4659207 : Nat := 4983230072969 + 3 ^ 40 * 4659207 * 2
def baseEnd_4659207 : Nat := 2392412659792857564885203

theorem tailTrace_4659207 : CollatzResearch.WordTrace tailWord_4659207 prefixEnd_4659207 2392412659792857564885203 := by
  unfold tailWord_4659207
  simp only [CollatzResearch.WordTrace]
  refine ⟨169935240031496243049471875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113290160020997495366314583 169935240031496243049471875)
  ·
    refine ⟨254902860047244364574207813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169935240031496243049471875 254902860047244364574207813)
    ·
      refine ⟨47794286258858318357663965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254902860047244364574207813 47794286258858318357663965)
      ·
        refine ⟨17922857347071869384123987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47794286258858318357663965 17922857347071869384123987)
        ·
          refine ⟨26884286020607804076185981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17922857347071869384123987 26884286020607804076185981)
          ·
            refine ⟨10081607257727926528569743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26884286020607804076185981 10081607257727926528569743)
            ·
              refine ⟨15122410886591889792854615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10081607257727926528569743 15122410886591889792854615)
              ·
                refine ⟨22683616329887834689281923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15122410886591889792854615 22683616329887834689281923)
                ·
                  refine ⟨34025424494831752033922885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22683616329887834689281923 34025424494831752033922885)
                  ·
                    refine ⟨6379767092780953506360541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34025424494831752033922885 6379767092780953506360541)
                    ·
                      refine ⟨2392412659792857564885203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379767092780953506360541 2392412659792857564885203)
                      ·
                        rfl

theorem cell23_4659207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4659207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659207 prefixEnd_4659207 := by exact prefixLift 4659207
  have htrace : WordTrace (prefixWord ++ tailWord_4659207) baseStart_4659207 baseEnd_4659207 := by
    simpa [prefixWord, tailWord_4659207, baseEnd_4659207] using wordTrace_append hprefix tailTrace_4659207
  have hstable : (prefixWord ++ tailWord_4659207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659207).length < 2 ^ (prefixWord ++ tailWord_4659207).sum := by decide
  have hdescent : baseEnd_4659207 < baseStart_4659207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659247 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 6, 3, 2]
def baseStart_4659247 : Nat := 118140960795 + 4659247 * 2 ^ 59
def prefixEnd_4659247 : Nat := 4983230072969 + 3 ^ 40 * 4659247 * 2
def baseEnd_4659247 : Nat := 2392433199019037408385019

theorem tailTrace_4659247 : CollatzResearch.WordTrace tailWord_4659247 prefixEnd_4659247 2392433199019037408385019 := by
  unfold tailWord_4659247
  simp only [CollatzResearch.WordTrace]
  refine ⟨169936698951351329880927995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113291132634234219920618663 169936698951351329880927995)
  ·
    refine ⟨254905048427026994821391993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169936698951351329880927995 254905048427026994821391993)
    ·
      refine ⟨191178786320270246116043995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254905048427026994821391993 191178786320270246116043995)
      ·
        refine ⟨286768179480405369174065993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191178786320270246116043995 286768179480405369174065993)
        ·
          refine ⟨215076134610304026880549495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286768179480405369174065993 215076134610304026880549495)
          ·
            refine ⟨322614201915456040320824243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215076134610304026880549495 322614201915456040320824243)
            ·
              refine ⟨483921302873184060481236365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322614201915456040320824243 483921302873184060481236365)
              ·
                refine ⟨181470488577444022680463637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483921302873184060481236365 181470488577444022680463637)
                ·
                  refine ⟨8506429152067688563146733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181470488577444022680463637 8506429152067688563146733)
                  ·
                    refine ⟨3189910932025383211180025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8506429152067688563146733 3189910932025383211180025)
                    ·
                      refine ⟨2392433199019037408385019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3189910932025383211180025 2392433199019037408385019)
                      ·
                        rfl

theorem cell23_4659247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3, 2].length) (baseStart_4659247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659247 prefixEnd_4659247 := by exact prefixLift 4659247
  have htrace : WordTrace (prefixWord ++ tailWord_4659247) baseStart_4659247 baseEnd_4659247 := by
    simpa [prefixWord, tailWord_4659247, baseEnd_4659247] using wordTrace_append hprefix tailTrace_4659247
  have hstable : (prefixWord ++ tailWord_4659247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659247).length < 2 ^ (prefixWord ++ tailWord_4659247).sum := by decide
  have hdescent : baseEnd_4659247 < baseStart_4659247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659287 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 4, 4]
def baseStart_4659287 : Nat := 118140960795 + 4659287 * 2 ^ 59
def prefixEnd_4659287 : Nat := 4983230072969 + 3 ^ 40 * 4659287 * 2
def baseEnd_4659287 : Nat := 797484579415072417294945

theorem tailTrace_4659287 : CollatzResearch.WordTrace tailWord_4659287 prefixEnd_4659287 797484579415072417294945 := by
  unfold tailWord_4659287
  simp only [CollatzResearch.WordTrace]
  refine ⟨169938157871206416712384115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113292105247470944474922743 169938157871206416712384115)
  ·
    refine ⟨254907236806809625068576173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169938157871206416712384115 254907236806809625068576173)
    ·
      refine ⟨95590213802553609400716065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254907236806809625068576173 95590213802553609400716065)
      ·
        refine ⟨71692660351915207050537049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95590213802553609400716065 71692660351915207050537049)
        ·
          refine ⟨53769495263936405287902787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71692660351915207050537049 53769495263936405287902787)
          ·
            refine ⟨80654242895904607931854181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53769495263936405287902787 80654242895904607931854181)
            ·
              refine ⟨15122670542982113987222659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80654242895904607931854181 15122670542982113987222659)
              ·
                refine ⟨22684005814473170980833989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15122670542982113987222659 22684005814473170980833989)
                ·
                  refine ⟨4253251090213719558906373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22684005814473170980833989 4253251090213719558906373)
                  ·
                    refine ⟨797484579415072417294945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4253251090213719558906373 797484579415072417294945)
                    ·
                      rfl

theorem cell23_4659287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_4659287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659287 prefixEnd_4659287 := by exact prefixLift 4659287
  have htrace : WordTrace (prefixWord ++ tailWord_4659287) baseStart_4659287 baseEnd_4659287 := by
    simpa [prefixWord, tailWord_4659287, baseEnd_4659287] using wordTrace_append hprefix tailTrace_4659287
  have hstable : (prefixWord ++ tailWord_4659287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659287).length < 2 ^ (prefixWord ++ tailWord_4659287).sum := by decide
  have hdescent : baseEnd_4659287 < baseStart_4659287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659288 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 1, 1, 3]
def baseStart_4659288 : Nat := 118140960795 + 4659288 * 2 ^ 59
def prefixEnd_4659288 : Nat := 4983230072969 + 3 ^ 40 * 4659288 * 2
def baseEnd_4659288 : Nat := 2392454251725871747972331

theorem tailTrace_4659288 : CollatzResearch.WordTrace tailWord_4659288 prefixEnd_4659288 2392454251725871747972331 := by
  unfold tailWord_4659288
  simp only [CollatzResearch.WordTrace]
  refine ⟨84969097172101396941585259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113292129562801862588780345 84969097172101396941585259)
  ·
    refine ⟨127453645758152095412377889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84969097172101396941585259 127453645758152095412377889)
    ·
      refine ⟨95590234318614071559283417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127453645758152095412377889 95590234318614071559283417)
      ·
        refine ⟨71692675738960553669462563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95590234318614071559283417 71692675738960553669462563)
        ·
          refine ⟨107539013608440830504193845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71692675738960553669462563 107539013608440830504193845)
          ·
            refine ⟨10081782525791327859768173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107539013608440830504193845 10081782525791327859768173)
            ·
              refine ⟨3780668447171747947413065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10081782525791327859768173 3780668447171747947413065)
              ·
                refine ⟨2835501335378810960559799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3780668447171747947413065 2835501335378810960559799)
                ·
                  refine ⟨4253252003068216440839699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835501335378810960559799 4253252003068216440839699)
                  ·
                    refine ⟨6379878004602324661259549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253252003068216440839699 6379878004602324661259549)
                    ·
                      refine ⟨2392454251725871747972331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379878004602324661259549 2392454251725871747972331)
                      ·
                        rfl

theorem cell23_4659288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_4659288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659288 prefixEnd_4659288 := by exact prefixLift 4659288
  have htrace : WordTrace (prefixWord ++ tailWord_4659288) baseStart_4659288 baseEnd_4659288 := by
    simpa [prefixWord, tailWord_4659288, baseEnd_4659288] using wordTrace_append hprefix tailTrace_4659288
  have hstable : (prefixWord ++ tailWord_4659288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659288).length < 2 ^ (prefixWord ++ tailWord_4659288).sum := by decide
  have hdescent : baseEnd_4659288 < baseStart_4659288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659290 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_4659290 : Nat := 118140960795 + 4659290 * 2 ^ 59
def prefixEnd_4659290 : Nat := 4983230072969 + 3 ^ 40 * 4659290 * 2
def baseEnd_4659290 : Nat := 2392455278687180740147321

theorem tailTrace_4659290 : CollatzResearch.WordTrace tailWord_4659290 prefixEnd_4659290 2392455278687180740147321 := by
  unfold tailWord_4659290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42484566822548887056185831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113292178193463698816495549 42484566822548887056185831)
  ·
    refine ⟨63726850233823330584278747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42484566822548887056185831 63726850233823330584278747)
    ·
      refine ⟨95590275350734995876418121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63726850233823330584278747 95590275350734995876418121)
      ·
        refine ⟨71692706513051246907313591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95590275350734995876418121 71692706513051246907313591)
        ·
          refine ⟨107539059769576870360970387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71692706513051246907313591 107539059769576870360970387)
          ·
            refine ⟨161308589654365305541455581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107539059769576870360970387 161308589654365305541455581)
            ·
              refine ⟨60490721120386989578045843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161308589654365305541455581 60490721120386989578045843)
              ·
                refine ⟨90736081680580484367068765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60490721120386989578045843 90736081680580484367068765)
                ·
                  refine ⟨34026030630217681637650787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90736081680580484367068765 34026030630217681637650787)
                  ·
                    refine ⟨51039045945326522456476181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34026030630217681637650787 51039045945326522456476181)
                    ·
                      refine ⟨2392455278687180740147321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51039045945326522456476181 2392455278687180740147321)
                      ·
                        rfl

theorem cell23_4659290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_4659290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659290 prefixEnd_4659290 := by exact prefixLift 4659290
  have htrace : WordTrace (prefixWord ++ tailWord_4659290) baseStart_4659290 baseEnd_4659290 := by
    simpa [prefixWord, tailWord_4659290, baseEnd_4659290] using wordTrace_append hprefix tailTrace_4659290
  have hstable : (prefixWord ++ tailWord_4659290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659290).length < 2 ^ (prefixWord ++ tailWord_4659290).sum := by decide
  have hdescent : baseEnd_4659290 < baseStart_4659290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659297 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_4659297 : Nat := 118140960795 + 4659297 * 2 ^ 59
def prefixEnd_4659297 : Nat := 4983230072969 + 3 ^ 40 * 4659297 * 2
def baseEnd_4659297 : Nat := 2392458873051762212759789

theorem tailTrace_4659297 : CollatzResearch.WordTrace tailWord_4659297 prefixEnd_4659297 2392458873051762212759789 := by
  unfold tailWord_4659297
  simp only [CollatzResearch.WordTrace]
  refine ⟨169938522601170188420248145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113292348400780125613498763 169938522601170188420248145)
  ·
    refine ⟨127453891950877641315186109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169938522601170188420248145 127453891950877641315186109)
    ·
      refine ⟨47795209481579115493194791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127453891950877641315186109 47795209481579115493194791)
      ·
        refine ⟨71692814222368673239792187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47795209481579115493194791 71692814222368673239792187)
        ·
          refine ⟨107539221333553009859688281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71692814222368673239792187 107539221333553009859688281)
          ·
            refine ⟨80654416000164757394766211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107539221333553009859688281 80654416000164757394766211)
            ·
              refine ⟨120981624000247136092149317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80654416000164757394766211 120981624000247136092149317)
              ·
                refine ⟨22684054500046338017277997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120981624000247136092149317 22684054500046338017277997)
                ·
                  refine ⟨8506520437517376756479249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22684054500046338017277997 8506520437517376756479249)
                  ·
                    refine ⟨6379890328138032567359437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8506520437517376756479249 6379890328138032567359437)
                    ·
                      refine ⟨2392458873051762212759789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379890328138032567359437 2392458873051762212759789)
                      ·
                        rfl

theorem cell23_4659297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_4659297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659297 prefixEnd_4659297 := by exact prefixLift 4659297
  have htrace : WordTrace (prefixWord ++ tailWord_4659297) baseStart_4659297 baseEnd_4659297 := by
    simpa [prefixWord, tailWord_4659297, baseEnd_4659297] using wordTrace_append hprefix tailTrace_4659297
  have hstable : (prefixWord ++ tailWord_4659297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659297).length < 2 ^ (prefixWord ++ tailWord_4659297).sum := by decide
  have hdescent : baseEnd_4659297 < baseStart_4659297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659300 : List Nat := [2, 3, 1, 1, 2, 1, 3, 10]
def baseStart_4659300 : Nat := 118140960795 + 4659300 * 2 ^ 59
def prefixEnd_4659300 : Nat := 4983230072969 + 3 ^ 40 * 4659300 * 2
def baseEnd_4659300 : Nat := 88609644944212063000825

theorem tailTrace_4659300 : CollatzResearch.WordTrace tailWord_4659300 prefixEnd_4659300 88609644944212063000825 := by
  unfold tailWord_4659300
  simp only [CollatzResearch.WordTrace]
  refine ⟨84969316010079659966303677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113292421346772879955071569 84969316010079659966303677)
  ·
    refine ⟨31863493503779872487363879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84969316010079659966303677 31863493503779872487363879)
    ·
      refine ⟨47795240255669808731045819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31863493503779872487363879 47795240255669808731045819)
      ·
        refine ⟨71692860383504713096568729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47795240255669808731045819 71692860383504713096568729)
        ·
          refine ⟨53769645287628534822426547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71692860383504713096568729 53769645287628534822426547)
          ·
            refine ⟨80654467931442802233639821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53769645287628534822426547 80654467931442802233639821)
            ·
              refine ⟨30245425474291050837614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80654467931442802233639821 30245425474291050837614933)
              ·
                refine ⟨88609644944212063000825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30245425474291050837614933 88609644944212063000825)
                ·
                  rfl

theorem cell23_4659300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 10].length) (baseStart_4659300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659300 prefixEnd_4659300 := by exact prefixLift 4659300
  have htrace : WordTrace (prefixWord ++ tailWord_4659300) baseStart_4659300 baseEnd_4659300 := by
    simpa [prefixWord, tailWord_4659300, baseEnd_4659300] using wordTrace_append hprefix tailTrace_4659300
  have hstable : (prefixWord ++ tailWord_4659300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659300).length < 2 ^ (prefixWord ++ tailWord_4659300).sum := by decide
  have hdescent : baseEnd_4659300 < baseStart_4659300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659314 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_4659314 : Nat := 118140960795 + 4659314 * 2 ^ 59
def prefixEnd_4659314 : Nat := 4983230072969 + 3 ^ 40 * 4659314 * 2
def baseEnd_4659314 : Nat := 2392467602222888646247211

theorem tailTrace_4659314 : CollatzResearch.WordTrace tailWord_4659314 prefixEnd_4659314 2392467602222888646247211 := by
  unfold tailWord_4659314
  simp only [CollatzResearch.WordTrace]
  refine ⟨42484785660527150080904249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113292761761405733549077997 42484785660527150080904249)
  ·
    refine ⟨31863589245395362560678187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42484785660527150080904249 31863589245395362560678187)
    ·
      refine ⟨47795383868093043841017281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31863589245395362560678187 47795383868093043841017281)
      ·
        refine ⟨35846537901069782880762961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47795383868093043841017281 35846537901069782880762961)
        ·
          refine ⟨26884903425802337160572221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35846537901069782880762961 26884903425802337160572221)
          ·
            refine ⟨10081838784675876435214583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26884903425802337160572221 10081838784675876435214583)
            ·
              refine ⟨15122758177013814652821875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10081838784675876435214583 15122758177013814652821875)
              ·
                refine ⟨22684137265520721979232813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15122758177013814652821875 22684137265520721979232813)
                ·
                  refine ⟨8506551474570270742212305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22684137265520721979232813 8506551474570270742212305)
                  ·
                    refine ⟨6379913605927703056659229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8506551474570270742212305 6379913605927703056659229)
                    ·
                      refine ⟨2392467602222888646247211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379913605927703056659229 2392467602222888646247211)
                      ·
                        rfl

theorem cell23_4659314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_4659314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659314 prefixEnd_4659314 := by exact prefixLift 4659314
  have htrace : WordTrace (prefixWord ++ tailWord_4659314) baseStart_4659314 baseEnd_4659314 := by
    simpa [prefixWord, tailWord_4659314, baseEnd_4659314] using wordTrace_append hprefix tailTrace_4659314
  have hstable : (prefixWord ++ tailWord_4659314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659314).length < 2 ^ (prefixWord ++ tailWord_4659314).sum := by decide
  have hdescent : baseEnd_4659314 < baseStart_4659314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659331 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 1, 2, 3]
def baseStart_4659331 : Nat := 118140960795 + 4659331 * 2 ^ 59
def prefixEnd_4659331 : Nat := 4983230072969 + 3 ^ 40 * 4659331 * 2
def baseEnd_4659331 : Nat := 2392476331394015079734633

theorem tailTrace_4659331 : CollatzResearch.WordTrace tailWord_4659331 prefixEnd_4659331 2392476331394015079734633 := by
  unfold tailWord_4659331
  simp only [CollatzResearch.WordTrace]
  refine ⟨169939762683047012226985847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113293175122031341484657231 169939762683047012226985847)
  ·
    refine ⟨254909644024570518340478771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169939762683047012226985847 254909644024570518340478771)
    ·
      refine ⟨382364466036855777510718157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254909644024570518340478771 382364466036855777510718157)
      ·
        refine ⟨143386674763820916566519309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382364466036855777510718157 143386674763820916566519309)
        ·
          refine ⟨53770003036432843712444741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143386674763820916566519309 53770003036432843712444741)
          ·
            refine ⟨10081875569331158196083389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53770003036432843712444741 10081875569331158196083389)
            ·
              refine ⟨3780703338499184323531271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10081875569331158196083389 3780703338499184323531271)
              ·
                refine ⟨5671055007748776485296907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780703338499184323531271 5671055007748776485296907)
                ·
                  refine ⟨8506582511623164727945361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671055007748776485296907 8506582511623164727945361)
                  ·
                    refine ⟨6379936883717373545959021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8506582511623164727945361 6379936883717373545959021)
                    ·
                      refine ⟨2392476331394015079734633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379936883717373545959021 2392476331394015079734633)
                      ·
                        rfl

theorem cell23_4659331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_4659331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659331 prefixEnd_4659331 := by exact prefixLift 4659331
  have htrace : WordTrace (prefixWord ++ tailWord_4659331) baseStart_4659331 baseEnd_4659331 := by
    simpa [prefixWord, tailWord_4659331, baseEnd_4659331] using wordTrace_append hprefix tailTrace_4659331
  have hstable : (prefixWord ++ tailWord_4659331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659331).length < 2 ^ (prefixWord ++ tailWord_4659331).sum := by decide
  have hdescent : baseEnd_4659331 < baseStart_4659331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659340 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4659340 : Nat := 118140960795 + 4659340 * 2 ^ 59
def prefixEnd_4659340 : Nat := 4983230072969 + 3 ^ 40 * 4659340 * 2
def baseEnd_4659340 : Nat := 2392480952719905544522091

theorem tailTrace_4659340 : CollatzResearch.WordTrace tailWord_4659340 prefixEnd_4659340 2392480952719905544522091 := by
  unfold tailWord_4659340
  simp only [CollatzResearch.WordTrace]
  refine ⟨84970045470007203382031737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113293393960009604509375649 84970045470007203382031737)
  ·
    refine ⟨63727534102505402536523803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84970045470007203382031737 63727534102505402536523803)
    ·
      refine ⟨95591301153758103804785705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63727534102505402536523803 95591301153758103804785705)
      ·
        refine ⟨71693475865318577853589279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95591301153758103804785705 71693475865318577853589279)
        ·
          refine ⟨107540213797977866780383919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71693475865318577853589279 107540213797977866780383919)
          ·
            refine ⟨161310320696966800170575879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107540213797977866780383919 161310320696966800170575879)
            ·
              refine ⟨241965481045450200255863819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161310320696966800170575879 241965481045450200255863819)
              ·
                refine ⟨362948221568175300383795729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241965481045450200255863819 362948221568175300383795729)
                ·
                  refine ⟨272211166176131475287846797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362948221568175300383795729 272211166176131475287846797)
                  ·
                    refine ⟨102079187316049303232942549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272211166176131475287846797 102079187316049303232942549)
                    ·
                      refine ⟨2392480952719905544522091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102079187316049303232942549 2392480952719905544522091)
                      ·
                        rfl

theorem cell23_4659340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4659340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659340 prefixEnd_4659340 := by exact prefixLift 4659340
  have htrace : WordTrace (prefixWord ++ tailWord_4659340) baseStart_4659340 baseEnd_4659340 := by
    simpa [prefixWord, tailWord_4659340, baseEnd_4659340] using wordTrace_append hprefix tailTrace_4659340
  have hstable : (prefixWord ++ tailWord_4659340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659340).length < 2 ^ (prefixWord ++ tailWord_4659340).sum := by decide
  have hdescent : baseEnd_4659340 < baseStart_4659340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659361 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4659361 : Nat := 118140960795 + 4659361 * 2 ^ 59
def prefixEnd_4659361 : Nat := 4983230072969 + 3 ^ 40 * 4659361 * 2
def baseEnd_4659361 : Nat := 2392491735813649962359495

theorem tailTrace_4659361 : CollatzResearch.WordTrace tailWord_4659361 prefixEnd_4659361 2392491735813649962359495 := by
  unfold tailWord_4659361
  simp only [CollatzResearch.WordTrace]
  refine ⟨169940856872938327350577937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113293904581958884900385291 169940856872938327350577937)
  ·
    refine ⟨127455642654703745512933453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169940856872938327350577937 127455642654703745512933453)
    ·
      refine ⟨47795865995513904567350045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127455642654703745512933453 47795865995513904567350045)
      ·
        refine ⟨17923449748317714212756267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47795865995513904567350045 17923449748317714212756267)
        ·
          refine ⟨26885174622476571319134401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17923449748317714212756267 26885174622476571319134401)
          ·
            refine ⟨20163880966857428489350801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26885174622476571319134401 20163880966857428489350801)
            ·
              refine ⟨15122910725143071367013101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20163880966857428489350801 15122910725143071367013101)
              ·
                refine ⟨5671091521928651762629913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15122910725143071367013101 5671091521928651762629913)
                ·
                  refine ⟨4253318641446488821972435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671091521928651762629913 4253318641446488821972435)
                  ·
                    refine ⟨6379977962169733232958653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253318641446488821972435 6379977962169733232958653)
                    ·
                      refine ⟨2392491735813649962359495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6379977962169733232958653 2392491735813649962359495)
                      ·
                        rfl

theorem cell23_4659361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4659361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659361 prefixEnd_4659361 := by exact prefixLift 4659361
  have htrace : WordTrace (prefixWord ++ tailWord_4659361) baseStart_4659361 baseEnd_4659361 := by
    simpa [prefixWord, tailWord_4659361, baseEnd_4659361] using wordTrace_append hprefix tailTrace_4659361
  have hstable : (prefixWord ++ tailWord_4659361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659361).length < 2 ^ (prefixWord ++ tailWord_4659361).sum := by decide
  have hdescent : baseEnd_4659361 < baseStart_4659361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659384 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 1, 4, 2]
def baseStart_4659384 : Nat := 118140960795 + 4659384 * 2 ^ 59
def prefixEnd_4659384 : Nat := 4983230072969 + 3 ^ 40 * 4659384 * 2
def baseEnd_4659384 : Nat := 2392503545868703372371889

theorem tailTrace_4659384 : CollatzResearch.WordTrace tailWord_4659384 prefixEnd_4659384 2392503545868703372371889 := by
  unfold tailWord_4659384
  simp only [CollatzResearch.WordTrace]
  refine ⟨84970847875927501139332603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113294463834570001519110137 84970847875927501139332603)
  ·
    refine ⟨127456271813891251708998905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84970847875927501139332603 127456271813891251708998905)
    ·
      refine ⟨95592203860418438781749179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127456271813891251708998905 95592203860418438781749179)
      ·
        refine ⟨143388305790627658172623769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95592203860418438781749179 143388305790627658172623769)
        ·
          refine ⟨107541229342970743629467827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143388305790627658172623769 107541229342970743629467827)
          ·
            refine ⟨161311844014456115444201741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107541229342970743629467827 161311844014456115444201741)
            ·
              refine ⟨60491941505421043291575653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161311844014456115444201741 60491941505421043291575653)
              ·
                refine ⟨11342239032266445617170435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60491941505421043291575653 11342239032266445617170435)
                ·
                  refine ⟨17013358548399668425755653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11342239032266445617170435 17013358548399668425755653)
                  ·
                    refine ⟨3190004727824937829829185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17013358548399668425755653 3190004727824937829829185)
                    ·
                      refine ⟨2392503545868703372371889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190004727824937829829185 2392503545868703372371889)
                      ·
                        rfl

theorem cell23_4659384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_4659384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659384 prefixEnd_4659384 := by exact prefixLift 4659384
  have htrace : WordTrace (prefixWord ++ tailWord_4659384) baseStart_4659384 baseEnd_4659384 := by
    simpa [prefixWord, tailWord_4659384, baseEnd_4659384] using wordTrace_append hprefix tailTrace_4659384
  have hstable : (prefixWord ++ tailWord_4659384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659384).length < 2 ^ (prefixWord ++ tailWord_4659384).sum := by decide
  have hdescent : baseEnd_4659384 < baseStart_4659384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659388 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_4659388 : Nat := 118140960795 + 4659388 * 2 ^ 59
def prefixEnd_4659388 : Nat := 4983230072969 + 3 ^ 40 * 4659388 * 2
def baseEnd_4659388 : Nat := 2392505599791321356721871

theorem tailTrace_4659388 : CollatzResearch.WordTrace tailWord_4659388 prefixEnd_4659388 2392505599791321356721871 := by
  unfold tailWord_4659388
  simp only [CollatzResearch.WordTrace]
  refine ⟨84970920821920255480905409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113294561095893673974540545 84970920821920255480905409)
  ·
    refine ⟨63728190616440191610679057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84970920821920255480905409 63728190616440191610679057)
    ·
      refine ⟨47796142962330143708009293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63728190616440191610679057 47796142962330143708009293)
      ·
        refine ⟨17923553610873803890503485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47796142962330143708009293 17923553610873803890503485)
        ·
          refine ⟨6721332604077676458938807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17923553610873803890503485 6721332604077676458938807)
          ·
            refine ⟨10081998906116514688408211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721332604077676458938807 10081998906116514688408211)
            ·
              refine ⟨15122998359174772032612317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10081998906116514688408211 15122998359174772032612317)
              ·
                refine ⟨5671124384690539512229619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15122998359174772032612317 5671124384690539512229619)
                ·
                  refine ⟨8506686577035809268344429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671124384690539512229619 8506686577035809268344429)
                  ·
                    refine ⟨3190007466388428475629161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8506686577035809268344429 3190007466388428475629161)
                    ·
                      refine ⟨2392505599791321356721871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190007466388428475629161 2392505599791321356721871)
                      ·
                        rfl

theorem cell23_4659388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_4659388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659388 prefixEnd_4659388 := by exact prefixLift 4659388
  have htrace : WordTrace (prefixWord ++ tailWord_4659388) baseStart_4659388 baseEnd_4659388 := by
    simpa [prefixWord, tailWord_4659388, baseEnd_4659388] using wordTrace_append hprefix tailTrace_4659388
  have hstable : (prefixWord ++ tailWord_4659388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659388).length < 2 ^ (prefixWord ++ tailWord_4659388).sum := by decide
  have hdescent : baseEnd_4659388 < baseStart_4659388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659397 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_4659397 : Nat := 118140960795 + 4659397 * 2 ^ 59
def prefixEnd_4659397 : Nat := 4983230072969 + 3 ^ 40 * 4659397 * 2
def baseEnd_4659397 : Nat := 2392510221117211821509329

theorem tailTrace_4659397 : CollatzResearch.WordTrace tailWord_4659397 prefixEnd_4659397 2392510221117211821509329 := by
  unfold tailWord_4659397
  simp only [CollatzResearch.WordTrace]
  refine ⟨169942169900807905498888445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113294779933871936999258963 169942169900807905498888445)
  ·
    refine ⟨63728313712802964562083167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169942169900807905498888445 63728313712802964562083167)
    ·
      refine ⟨95592470569204446843124751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63728313712802964562083167 95592470569204446843124751)
      ·
        refine ⟨143388705853806670264687127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95592470569204446843124751 143388705853806670264687127)
        ·
          refine ⟨215083058780710005397030691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143388705853806670264687127 215083058780710005397030691)
          ·
            refine ⟨322624588171065008095546037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215083058780710005397030691 322624588171065008095546037)
            ·
              refine ⟨30246055141037344508957441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322624588171065008095546037 30246055141037344508957441)
              ·
                refine ⟨22684541355778008381718081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30246055141037344508957441 22684541355778008381718081)
                ·
                  refine ⟨17013406016833506286288561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22684541355778008381718081 17013406016833506286288561)
                  ·
                    refine ⟨12760054512625129714716421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17013406016833506286288561 12760054512625129714716421)
                    ·
                      refine ⟨2392510221117211821509329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12760054512625129714716421 2392510221117211821509329)
                      ·
                        rfl

theorem cell23_4659397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_4659397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659397 prefixEnd_4659397 := by exact prefixLift 4659397
  have htrace : WordTrace (prefixWord ++ tailWord_4659397) baseStart_4659397 baseEnd_4659397 := by
    simpa [prefixWord, tailWord_4659397, baseEnd_4659397] using wordTrace_append hprefix tailTrace_4659397
  have hstable : (prefixWord ++ tailWord_4659397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659397).length < 2 ^ (prefixWord ++ tailWord_4659397).sum := by decide
  have hdescent : baseEnd_4659397 < baseStart_4659397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659401 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 2, 2, 2]
def baseStart_4659401 : Nat := 118140960795 + 4659401 * 2 ^ 59
def prefixEnd_4659401 : Nat := 4983230072969 + 3 ^ 40 * 4659401 * 2
def baseEnd_4659401 : Nat := 2392512275039829805859311

theorem tailTrace_4659401 : CollatzResearch.WordTrace tailWord_4659401 prefixEnd_4659401 2392512275039829805859311 := by
  unfold tailWord_4659401
  simp only [CollatzResearch.WordTrace]
  refine ⟨169942315792793414182034057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113294877195195609454689371 169942315792793414182034057)
  ·
    refine ⟨127456736844595060636525543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169942315792793414182034057 127456736844595060636525543)
    ·
      refine ⟨191185105266892590954788315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127456736844595060636525543 191185105266892590954788315)
      ·
        refine ⟨286777657900338886432182473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191185105266892590954788315 286777657900338886432182473)
        ·
          refine ⟨215083243425254164824136855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286777657900338886432182473 215083243425254164824136855)
          ·
            refine ⟨322624865137881247236205283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215083243425254164824136855 322624865137881247236205283)
            ·
              refine ⟨483937297706821870854307925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322624865137881247236205283 483937297706821870854307925)
              ·
                refine ⟨5671140207501818799073921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 483937297706821870854307925 5671140207501818799073921)
                ·
                  refine ⟨4253355155626364099305441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671140207501818799073921 4253355155626364099305441)
                  ·
                    refine ⟨3190016366719773074479081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4253355155626364099305441 3190016366719773074479081)
                    ·
                      refine ⟨2392512275039829805859311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190016366719773074479081 2392512275039829805859311)
                      ·
                        rfl

theorem cell23_4659401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 2, 2].length) (baseStart_4659401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659401 prefixEnd_4659401 := by exact prefixLift 4659401
  have htrace : WordTrace (prefixWord ++ tailWord_4659401) baseStart_4659401 baseEnd_4659401 := by
    simpa [prefixWord, tailWord_4659401, baseEnd_4659401] using wordTrace_append hprefix tailTrace_4659401
  have hstable : (prefixWord ++ tailWord_4659401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659401).length < 2 ^ (prefixWord ++ tailWord_4659401).sum := by decide
  have hdescent : baseEnd_4659401 < baseStart_4659401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659407 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 7]
def baseStart_4659407 : Nat := 118140960795 + 4659407 * 2 ^ 59
def prefixEnd_4659407 : Nat := 4983230072969 + 3 ^ 40 * 4659407 * 2
def baseEnd_4659407 : Nat := 265835039547084086931587

theorem tailTrace_4659407 : CollatzResearch.WordTrace tailWord_4659407 prefixEnd_4659407 265835039547084086931587 := by
  unfold tailWord_4659407
  simp only [CollatzResearch.WordTrace]
  refine ⟨169942534630771677206752475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113295023087181118137834983 169942534630771677206752475)
  ·
    refine ⟨254913801946157515810128713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169942534630771677206752475 254913801946157515810128713)
    ·
      refine ⟨191185351459618136857596535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254913801946157515810128713 191185351459618136857596535)
      ·
        refine ⟨286778027189427205286394803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191185351459618136857596535 286778027189427205286394803)
        ·
          refine ⟨430167040784140807929592205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286778027189427205286394803 430167040784140807929592205)
          ·
            refine ⟨161312640294052802973597077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 430167040784140807929592205 161312640294052802973597077)
            ·
              refine ⟨7561530013783725139387363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161312640294052802973597077 7561530013783725139387363)
              ·
                refine ⟨11342295020675587709081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7561530013783725139387363 11342295020675587709081045)
                ·
                  refine ⟨265835039547084086931587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11342295020675587709081045 265835039547084086931587)
                  ·
                    rfl

theorem cell23_4659407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 7].length) (baseStart_4659407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659407 prefixEnd_4659407 := by exact prefixLift 4659407
  have htrace : WordTrace (prefixWord ++ tailWord_4659407) baseStart_4659407 baseEnd_4659407 := by
    simpa [prefixWord, tailWord_4659407, baseEnd_4659407] using wordTrace_append hprefix tailTrace_4659407
  have hstable : (prefixWord ++ tailWord_4659407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659407).length < 2 ^ (prefixWord ++ tailWord_4659407).sum := by decide
  have hdescent : baseEnd_4659407 < baseStart_4659407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659464 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_4659464 : Nat := 118140960795 + 4659464 * 2 ^ 59
def prefixEnd_4659464 : Nat := 4983230072969 + 3 ^ 40 * 4659464 * 2
def baseEnd_4659464 : Nat := 2392544624321063059371521

theorem tailTrace_4659464 : CollatzResearch.WordTrace tailWord_4659464 prefixEnd_4659464 2392544624321063059371521 := by
  unfold tailWord_4659464
  simp only [CollatzResearch.WordTrace]
  refine ⟨84972306795782587970788723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113296409061043450627718297 84972306795782587970788723)
  ·
    refine ⟨127458460193673881956183085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84972306795782587970788723 127458460193673881956183085)
    ·
      refine ⟨47796922572627705733568657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127458460193673881956183085 47796922572627705733568657)
      ·
        refine ⟨35847691929470779300176493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47796922572627705733568657 35847691929470779300176493)
        ·
          refine ⟨13442884473551542237566185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35847691929470779300176493 13442884473551542237566185)
          ·
            refine ⟨10082163355163656678174639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13442884473551542237566185 10082163355163656678174639)
            ·
              refine ⟨15123245032745485017261959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10082163355163656678174639 15123245032745485017261959)
              ·
                refine ⟨22684867549118227525892939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15123245032745485017261959 22684867549118227525892939)
                ·
                  refine ⟨34027301323677341288839409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22684867549118227525892939 34027301323677341288839409)
                  ·
                    refine ⟨25520475992758005966629557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34027301323677341288839409 25520475992758005966629557)
                    ·
                      refine ⟨2392544624321063059371521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25520475992758005966629557 2392544624321063059371521)
                      ·
                        rfl

theorem cell23_4659464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_4659464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659464 prefixEnd_4659464 := by exact prefixLift 4659464
  have htrace : WordTrace (prefixWord ++ tailWord_4659464) baseStart_4659464 baseEnd_4659464 := by
    simpa [prefixWord, tailWord_4659464, baseEnd_4659464] using wordTrace_append hprefix tailTrace_4659464
  have hstable : (prefixWord ++ tailWord_4659464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659464).length < 2 ^ (prefixWord ++ tailWord_4659464).sum := by decide
  have hdescent : baseEnd_4659464 < baseStart_4659464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659484 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_4659484 : Nat := 118140960795 + 4659484 * 2 ^ 59
def prefixEnd_4659484 : Nat := 4983230072969 + 3 ^ 40 * 4659484 * 2
def baseEnd_4659484 : Nat := 797518297978050993707143

theorem tailTrace_4659484 : CollatzResearch.WordTrace tailWord_4659484 prefixEnd_4659484 797518297978050993707143 := by
  unfold tailWord_4659484
  simp only [CollatzResearch.WordTrace]
  refine ⟨84972671525746359678652753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113296895367661812904870337 84972671525746359678652753)
  ·
    refine ⟨63729503644309769758989565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84972671525746359678652753 63729503644309769758989565)
    ·
      refine ⟨23898563866616163659621087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63729503644309769758989565 23898563866616163659621087)
      ·
        refine ⟨35847845799924245489431631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23898563866616163659621087 35847845799924245489431631)
        ·
          refine ⟨53771768699886368234147447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35847845799924245489431631 53771768699886368234147447)
          ·
            refine ⟨80657653049829552351221171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53771768699886368234147447 80657653049829552351221171)
            ·
              refine ⟨120986479574744328526831757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80657653049829552351221171 120986479574744328526831757)
              ·
                refine ⟨45369929840529123197561909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120986479574744328526831757 45369929840529123197561909)
                ·
                  refine ⟨4253430922549605299771429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45369929840529123197561909 4253430922549605299771429)
                  ·
                    refine ⟨797518297978050993707143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4253430922549605299771429 797518297978050993707143)
                    ·
                      rfl

theorem cell23_4659484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_4659484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659484 prefixEnd_4659484 := by exact prefixLift 4659484
  have htrace : WordTrace (prefixWord ++ tailWord_4659484) baseStart_4659484 baseEnd_4659484 := by
    simpa [prefixWord, tailWord_4659484, baseEnd_4659484] using wordTrace_append hprefix tailTrace_4659484
  have hstable : (prefixWord ++ tailWord_4659484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659484).length < 2 ^ (prefixWord ++ tailWord_4659484).sum := by decide
  have hdescent : baseEnd_4659484 < baseStart_4659484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659514 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_4659514 : Nat := 118140960795 + 4659514 * 2 ^ 59
def prefixEnd_4659514 : Nat := 4983230072969 + 3 ^ 40 * 4659514 * 2
def baseEnd_4659514 : Nat := 265841144261531984860699

theorem tailTrace_4659514 : CollatzResearch.WordTrace tailWord_4659514 prefixEnd_4659514 265841144261531984860699 := by
  unfold tailWord_4659514
  simp only [CollatzResearch.WordTrace]
  refine ⟨42486609310346008620224399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113297624827589356320598397 42486609310346008620224399)
  ·
    refine ⟨63729913965519012930336599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42486609310346008620224399 63729913965519012930336599)
    ·
      refine ⟨95594870948278519395504899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63729913965519012930336599 95594870948278519395504899)
      ·
        refine ⟨143392306422417779093257349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95594870948278519395504899 143392306422417779093257349)
        ·
          refine ⟨26886057454203333579985753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143392306422417779093257349 26886057454203333579985753)
          ·
            refine ⟨20164543090652500184989315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26886057454203333579985753 20164543090652500184989315)
            ·
              refine ⟨30246814635978750277483973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20164543090652500184989315 30246814635978750277483973)
              ·
                refine ⟨5671277744246015677028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30246814635978750277483973 5671277744246015677028245)
                ·
                  refine ⟨265841144261531984860699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5671277744246015677028245 265841144261531984860699)
                  ·
                    rfl

theorem cell23_4659514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_4659514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659514 prefixEnd_4659514 := by exact prefixLift 4659514
  have htrace : WordTrace (prefixWord ++ tailWord_4659514) baseStart_4659514 baseEnd_4659514 := by
    simpa [prefixWord, tailWord_4659514, baseEnd_4659514] using wordTrace_append hprefix tailTrace_4659514
  have hstable : (prefixWord ++ tailWord_4659514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659514).length < 2 ^ (prefixWord ++ tailWord_4659514).sum := by decide
  have hdescent : baseEnd_4659514 < baseStart_4659514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659598 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4659598 : Nat := 118140960795 + 4659598 * 2 ^ 59
def prefixEnd_4659598 : Nat := 4983230072969 + 3 ^ 40 * 4659598 * 2
def baseEnd_4659598 : Nat := 2392613430728765535095905

theorem tailTrace_4659598 : CollatzResearch.WordTrace tailWord_4659598 prefixEnd_4659598 2392613430728765535095905 := by
  unfold tailWord_4659598
  simp only [CollatzResearch.WordTrace]
  refine ⟨21243687621634964603369431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113299667315386477884636965 21243687621634964603369431)
  ·
    refine ⟨31865531432452446905054147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21243687621634964603369431 31865531432452446905054147)
    ·
      refine ⟨47798297148678670357581221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31865531432452446905054147 47798297148678670357581221)
      ·
        refine ⟨8962180715377250692046479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47798297148678670357581221 8962180715377250692046479)
        ·
          refine ⟨13443271073065876038069719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8962180715377250692046479 13443271073065876038069719)
          ·
            refine ⟨20164906609598814057104579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13443271073065876038069719 20164906609598814057104579)
            ·
              refine ⟨30247359914398221085656869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20164906609598814057104579 30247359914398221085656869)
              ·
                refine ⟨5671379983949666453560663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30247359914398221085656869 5671379983949666453560663)
                ·
                  refine ⟨8507069975924499680340995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671379983949666453560663 8507069975924499680340995)
                  ·
                    refine ⟨12760604963886749520511493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8507069975924499680340995 12760604963886749520511493)
                    ·
                      refine ⟨2392613430728765535095905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12760604963886749520511493 2392613430728765535095905)
                      ·
                        rfl

theorem cell23_4659598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4659598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659598 prefixEnd_4659598 := by exact prefixLift 4659598
  have htrace : WordTrace (prefixWord ++ tailWord_4659598) baseStart_4659598 baseEnd_4659598 := by
    simpa [prefixWord, tailWord_4659598, baseEnd_4659598] using wordTrace_append hprefix tailTrace_4659598
  have hstable : (prefixWord ++ tailWord_4659598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659598).length < 2 ^ (prefixWord ++ tailWord_4659598).sum := by decide
  have hdescent : baseEnd_4659598 < baseStart_4659598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659618 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4659618 : Nat := 118140960795 + 4659618 * 2 ^ 59
def prefixEnd_4659618 : Nat := 4983230072969 + 3 ^ 40 * 4659618 * 2
def baseEnd_4659618 : Nat := 2392623700341855456845813

theorem tailTrace_4659618 : CollatzResearch.WordTrace tailWord_4659618 prefixEnd_4659618 2392623700341855456845813 := by
  unfold tailWord_4659618
  simp only [CollatzResearch.WordTrace]
  refine ⟨42487557608251815060670877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113300153622004840161789005 42487557608251815060670877)
  ·
    refine ⟨15932834103094430647751579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42487557608251815060670877 15932834103094430647751579)
    ·
      refine ⟨23899251154641645971627369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15932834103094430647751579 23899251154641645971627369)
      ·
        refine ⟨17924438365981234478720527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23899251154641645971627369 17924438365981234478720527)
        ·
          refine ⟨26886657548971851718080791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17924438365981234478720527 26886657548971851718080791)
          ·
            refine ⟨40329986323457777577121187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26886657548971851718080791 40329986323457777577121187)
            ·
              refine ⟨60494979485186666365681781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40329986323457777577121187 60494979485186666365681781)
              ·
                refine ⟨5671404326736249971782667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60494979485186666365681781 5671404326736249971782667)
                ·
                  refine ⟨8507106490104374957674001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671404326736249971782667 8507106490104374957674001)
                  ·
                    refine ⟨6380329867578281218255501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8507106490104374957674001 6380329867578281218255501)
                    ·
                      refine ⟨2392623700341855456845813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6380329867578281218255501 2392623700341855456845813)
                      ·
                        rfl

theorem cell23_4659618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4659618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659618 prefixEnd_4659618 := by exact prefixLift 4659618
  have htrace : WordTrace (prefixWord ++ tailWord_4659618) baseStart_4659618 baseEnd_4659618 := by
    simpa [prefixWord, tailWord_4659618, baseEnd_4659618] using wordTrace_append hprefix tailTrace_4659618
  have hstable : (prefixWord ++ tailWord_4659618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659618).length < 2 ^ (prefixWord ++ tailWord_4659618).sum := by decide
  have hdescent : baseEnd_4659618 < baseStart_4659618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659626 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4659626 : Nat := 118140960795 + 4659626 * 2 ^ 59
def prefixEnd_4659626 : Nat := 4983230072969 + 3 ^ 40 * 4659626 * 2
def baseEnd_4659626 : Nat := 2392627808187091425545777

theorem tailTrace_4659626 : CollatzResearch.WordTrace tailWord_4659626 prefixEnd_4659626 2392627808187091425545777 := by
  unfold tailWord_4659626
  simp only [CollatzResearch.WordTrace]
  refine ⟨42487630554244569402243683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113300348144652185072649821 42487630554244569402243683)
  ·
    refine ⟨63731445831366854103365525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42487630554244569402243683 63731445831366854103365525)
    ·
      refine ⟨2987411523345321286095259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63731445831366854103365525 2987411523345321286095259)
      ·
        refine ⟨4481117285017981929142889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2987411523345321286095259 4481117285017981929142889)
        ·
          refine ⟨3360837963763486446857167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481117285017981929142889 3360837963763486446857167)
          ·
            refine ⟨5041256945645229670285751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360837963763486446857167 5041256945645229670285751)
            ·
              refine ⟨7561885418467844505428627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041256945645229670285751 7561885418467844505428627)
              ·
                refine ⟨11342828127701766758142941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7561885418467844505428627 11342828127701766758142941)
                ·
                  refine ⟨4253560547888162534303603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11342828127701766758142941 4253560547888162534303603)
                  ·
                    refine ⟨6380340821832243801455405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253560547888162534303603 6380340821832243801455405)
                    ·
                      refine ⟨2392627808187091425545777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6380340821832243801455405 2392627808187091425545777)
                      ·
                        rfl

theorem cell23_4659626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4659626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659626 prefixEnd_4659626 := by exact prefixLift 4659626
  have htrace : WordTrace (prefixWord ++ tailWord_4659626) baseStart_4659626 baseEnd_4659626 := by
    simpa [prefixWord, tailWord_4659626, baseEnd_4659626] using wordTrace_append hprefix tailTrace_4659626
  have hstable : (prefixWord ++ tailWord_4659626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659626).length < 2 ^ (prefixWord ++ tailWord_4659626).sum := by decide
  have hdescent : baseEnd_4659626 < baseStart_4659626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659634 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_4659634 : Nat := 118140960795 + 4659634 * 2 ^ 59
def prefixEnd_4659634 : Nat := 4983230072969 + 3 ^ 40 * 4659634 * 2
def baseEnd_4659634 : Nat := 797543972010775798081913

theorem tailTrace_4659634 : CollatzResearch.WordTrace tailWord_4659634 prefixEnd_4659634 797543972010775798081913 := by
  unfold tailWord_4659634
  simp only [CollatzResearch.WordTrace]
  refine ⟨42487703500237323743816489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113300542667299529983510637 42487703500237323743816489)
  ·
    refine ⟨31865777625177992807862367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42487703500237323743816489 31865777625177992807862367)
    ·
      refine ⟨47798666437766989211793551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31865777625177992807862367 47798666437766989211793551)
      ·
        refine ⟨71697999656650483817690327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47798666437766989211793551 71697999656650483817690327)
        ·
          refine ⟨107546999484975725726535491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71697999656650483817690327 107546999484975725726535491)
          ·
            refine ⟨161320499227463588589803237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107546999484975725726535491 161320499227463588589803237)
            ·
              refine ⟨30247593605149422860588107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161320499227463588589803237 30247593605149422860588107)
              ·
                refine ⟨45371390407724134290882161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30247593605149422860588107 45371390407724134290882161)
                ·
                  refine ⟨34028542805793100718161621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45371390407724134290882161 34028542805793100718161621)
                  ·
                    refine ⟨797543972010775798081913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34028542805793100718161621 797543972010775798081913)
                    ·
                      rfl

theorem cell23_4659634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_4659634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659634 prefixEnd_4659634 := by exact prefixLift 4659634
  have htrace : WordTrace (prefixWord ++ tailWord_4659634) baseStart_4659634 baseEnd_4659634 := by
    simpa [prefixWord, tailWord_4659634, baseEnd_4659634] using wordTrace_append hprefix tailTrace_4659634
  have hstable : (prefixWord ++ tailWord_4659634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659634).length < 2 ^ (prefixWord ++ tailWord_4659634).sum := by decide
  have hdescent : baseEnd_4659634 < baseStart_4659634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659649 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4659649 : Nat := 118140960795 + 4659649 * 2 ^ 59
def prefixEnd_4659649 : Nat := 4983230072969 + 3 ^ 40 * 4659649 * 2
def baseEnd_4659649 : Nat := 2392639618242144835558171

theorem tailTrace_4659649 : CollatzResearch.WordTrace tailWord_4659649 prefixEnd_4659649 2392639618242144835558171 := by
  unfold tailWord_4659649
  simp only [CollatzResearch.WordTrace]
  refine ⟨169951361095894952537062001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113300907397263301691374667 169951361095894952537062001)
  ·
    refine ⟨127463520821921214402796501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169951361095894952537062001 127463520821921214402796501)
    ·
      refine ⟨2987426269263778462565543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 127463520821921214402796501 2987426269263778462565543)
      ·
        refine ⟨4481139403895667693848315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2987426269263778462565543 4481139403895667693848315)
        ·
          refine ⟨6721709105843501540772473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481139403895667693848315 6721709105843501540772473)
          ·
            refine ⟨5041281829382626155579355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721709105843501540772473 5041281829382626155579355)
            ·
              refine ⟨7561922744073939233369033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041281829382626155579355 7561922744073939233369033)
              ·
                refine ⟨5671442058055454425026775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7561922744073939233369033 5671442058055454425026775)
                ·
                  refine ⟨8507163087083181637540163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671442058055454425026775 8507163087083181637540163)
                  ·
                    refine ⟨12760744630624772456310245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8507163087083181637540163 12760744630624772456310245)
                    ·
                      refine ⟨2392639618242144835558171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12760744630624772456310245 2392639618242144835558171)
                      ·
                        rfl

theorem cell23_4659649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4659649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659649 prefixEnd_4659649 := by exact prefixLift 4659649
  have htrace : WordTrace (prefixWord ++ tailWord_4659649) baseStart_4659649 baseEnd_4659649 := by
    simpa [prefixWord, tailWord_4659649, baseEnd_4659649] using wordTrace_append hprefix tailTrace_4659649
  have hstable : (prefixWord ++ tailWord_4659649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659649).length < 2 ^ (prefixWord ++ tailWord_4659649).sum := by decide
  have hdescent : baseEnd_4659649 < baseStart_4659649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659652 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4659652 : Nat := 118140960795 + 4659652 * 2 ^ 59
def prefixEnd_4659652 : Nat := 4983230072969 + 3 ^ 40 * 4659652 * 2
def baseEnd_4659652 : Nat := 2392641158684108323820657

theorem tailTrace_4659652 : CollatzResearch.WordTrace tailWord_4659652 prefixEnd_4659652 2392641158684108323820657 := by
  unfold tailWord_4659652
  simp only [CollatzResearch.WordTrace]
  refine ⟨84975735257442042024710605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113300980343256056032947473 84975735257442042024710605)
  ·
    refine ⟨31865900721540765759266477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84975735257442042024710605 31865900721540765759266477)
    ·
      refine ⟨11949712770577787159724929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31865900721540765759266477 11949712770577787159724929)
      ·
        refine ⟨8962284577933340369793697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11949712770577787159724929 8962284577933340369793697)
        ·
          refine ⟨6721713433450005277345273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8962284577933340369793697 6721713433450005277345273)
          ·
            refine ⟨5041285075087503958008955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721713433450005277345273 5041285075087503958008955)
            ·
              refine ⟨7561927612631255937013433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041285075087503958008955 7561927612631255937013433)
              ·
                refine ⟨5671445709473441952760075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7561927612631255937013433 5671445709473441952760075)
                ·
                  refine ⟨8507168564210162929140113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671445709473441952760075 8507168564210162929140113)
                  ·
                    refine ⟨6380376423157622196855085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8507168564210162929140113 6380376423157622196855085)
                    ·
                      refine ⟨2392641158684108323820657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6380376423157622196855085 2392641158684108323820657)
                      ·
                        rfl

theorem cell23_4659652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4659652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659652 prefixEnd_4659652 := by exact prefixLift 4659652
  have htrace : WordTrace (prefixWord ++ tailWord_4659652) baseStart_4659652 baseEnd_4659652 := by
    simpa [prefixWord, tailWord_4659652, baseEnd_4659652] using wordTrace_append hprefix tailTrace_4659652
  have hstable : (prefixWord ++ tailWord_4659652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659652).length < 2 ^ (prefixWord ++ tailWord_4659652).sum := by decide
  have hdescent : baseEnd_4659652 < baseStart_4659652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659658 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_4659658 : Nat := 118140960795 + 4659658 * 2 ^ 59
def prefixEnd_4659658 : Nat := 4983230072969 + 3 ^ 40 * 4659658 * 2
def baseEnd_4659658 : Nat := 2392644239568035300345629

theorem tailTrace_4659658 : CollatzResearch.WordTrace tailWord_4659658 prefixEnd_4659658 2392644239568035300345629 := by
  unfold tailWord_4659658
  simp only [CollatzResearch.WordTrace]
  refine ⟨42487922338215586768534907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113301126235241564716093085 42487922338215586768534907)
  ·
    refine ⟨63731883507323380152802361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42487922338215586768534907 63731883507323380152802361)
    ·
      refine ⟨47798912630492535114601771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63731883507323380152802361 47798912630492535114601771)
      ·
        refine ⟨71698368945738802671902657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47798912630492535114601771 71698368945738802671902657)
        ·
          refine ⟨53773776709304102003926993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71698368945738802671902657 53773776709304102003926993)
          ·
            refine ⟨40330332531978076502945245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53773776709304102003926993 40330332531978076502945245)
            ·
              refine ⟨15123874699491778688604467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40330332531978076502945245 15123874699491778688604467)
              ·
                refine ⟨22685812049237668032906701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15123874699491778688604467 22685812049237668032906701)
                ·
                  refine ⟨8507179518464125512340013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22685812049237668032906701 8507179518464125512340013)
                  ·
                    refine ⟨3190192319424047067127505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8507179518464125512340013 3190192319424047067127505)
                    ·
                      refine ⟨2392644239568035300345629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190192319424047067127505 2392644239568035300345629)
                      ·
                        rfl

theorem cell23_4659658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_4659658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659658 prefixEnd_4659658 := by exact prefixLift 4659658
  have htrace : WordTrace (prefixWord ++ tailWord_4659658) baseStart_4659658 baseEnd_4659658 := by
    simpa [prefixWord, tailWord_4659658, baseEnd_4659658] using wordTrace_append hprefix tailTrace_4659658
  have hstable : (prefixWord ++ tailWord_4659658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659658).length < 2 ^ (prefixWord ++ tailWord_4659658).sum := by decide
  have hdescent : baseEnd_4659658 < baseStart_4659658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659684 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_4659684 : Nat := 118140960795 + 4659684 * 2 ^ 59
def prefixEnd_4659684 : Nat := 4983230072969 + 3 ^ 40 * 4659684 * 2
def baseEnd_4659684 : Nat := 2392657590065052198620509

theorem tailTrace_4659684 : CollatzResearch.WordTrace tailWord_4659684 prefixEnd_4659684 2392657590065052198620509 := by
  unfold tailWord_4659684
  simp only [CollatzResearch.WordTrace]
  refine ⟨84976318825384076757293053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113301758433845435676390737 84976318825384076757293053)
  ·
    refine ⟨31866119559519028783984895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84976318825384076757293053 31866119559519028783984895)
    ·
      refine ⟨47799179339278543175977343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31866119559519028783984895 47799179339278543175977343)
      ·
        refine ⟨71698769008917814763966015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47799179339278543175977343 71698769008917814763966015)
        ·
          refine ⟨107548153513376722145949023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71698769008917814763966015 107548153513376722145949023)
          ·
            refine ⟨161322230270065083218923535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107548153513376722145949023 161322230270065083218923535)
            ·
              refine ⟨241983345405097624828385303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161322230270065083218923535 241983345405097624828385303)
              ·
                refine ⟨362975018107646437242577955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241983345405097624828385303 362975018107646437242577955)
                ·
                  refine ⟨544462527161469655863866933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362975018107646437242577955 544462527161469655863866933)
                  ·
                    refine ⟨51043361921387780237237525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 544462527161469655863866933 51043361921387780237237525)
                    ·
                      refine ⟨2392657590065052198620509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51043361921387780237237525 2392657590065052198620509)
                      ·
                        rfl

theorem cell23_4659684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_4659684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659684 prefixEnd_4659684 := by exact prefixLift 4659684
  have htrace : WordTrace (prefixWord ++ tailWord_4659684) baseStart_4659684 baseEnd_4659684 := by
    simpa [prefixWord, tailWord_4659684, baseEnd_4659684] using wordTrace_append hprefix tailTrace_4659684
  have hstable : (prefixWord ++ tailWord_4659684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659684).length < 2 ^ (prefixWord ++ tailWord_4659684).sum := by decide
  have hdescent : baseEnd_4659684 < baseStart_4659684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659698 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_4659698 : Nat := 118140960795 + 4659698 * 2 ^ 59
def prefixEnd_4659698 : Nat := 4983230072969 + 3 ^ 40 * 4659698 * 2
def baseEnd_4659698 : Nat := 797554926264738381281815

theorem tailTrace_4659698 : CollatzResearch.WordTrace tailWord_4659698 prefixEnd_4659698 797554926264738381281815 := by
  unfold tailWord_4659698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42488287068179358476398937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113302098848478289270397165 42488287068179358476398937)
  ·
    refine ⟨31866215301134518857299203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42488287068179358476398937 31866215301134518857299203)
    ·
      refine ⟨47799322951701778285948805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31866215301134518857299203 47799322951701778285948805)
      ·
        refine ⟨8962373053444083428615401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47799322951701778285948805 8962373053444083428615401)
        ·
          refine ⟨6721779790083062571461551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8962373053444083428615401 6721779790083062571461551)
          ·
            refine ⟨10082669685124593857192327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721779790083062571461551 10082669685124593857192327)
            ·
              refine ⟨15124004527686890785788491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10082669685124593857192327 15124004527686890785788491)
              ·
                refine ⟨22686006791530336178682737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15124004527686890785788491 22686006791530336178682737)
                ·
                  refine ⟨17014505093647752134012053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22686006791530336178682737 17014505093647752134012053)
                  ·
                    refine ⟨797554926264738381281815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17014505093647752134012053 797554926264738381281815)
                    ·
                      rfl

theorem cell23_4659698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_4659698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659698 prefixEnd_4659698 := by exact prefixLift 4659698
  have htrace : WordTrace (prefixWord ++ tailWord_4659698) baseStart_4659698 baseEnd_4659698 := by
    simpa [prefixWord, tailWord_4659698, baseEnd_4659698] using wordTrace_append hprefix tailTrace_4659698
  have hstable : (prefixWord ++ tailWord_4659698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659698).length < 2 ^ (prefixWord ++ tailWord_4659698).sum := by decide
  have hdescent : baseEnd_4659698 < baseStart_4659698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659705 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 2, 2, 2]
def baseStart_4659705 : Nat := 118140960795 + 4659705 * 2 ^ 59
def prefixEnd_4659705 : Nat := 4983230072969 + 3 ^ 40 * 4659705 * 2
def baseEnd_4659705 : Nat := 2392668373158796616457913

theorem tailTrace_4659705 : CollatzResearch.WordTrace tailWord_4659705 prefixEnd_4659705 2392668373158796616457913 := by
  unfold tailWord_4659705
  simp only [CollatzResearch.WordTrace]
  refine ⟨169953403583692074101100569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113302269055794716067400379 169953403583692074101100569)
  ·
    refine ⟨127465052687769055575825427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169953403583692074101100569 127465052687769055575825427)
    ·
      refine ⟨191197579031653583363738141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127465052687769055575825427 191197579031653583363738141)
      ·
        refine ⟨71699092136870093761401803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191197579031653583363738141 71699092136870093761401803)
        ·
          refine ⟨107548638205305140642102705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71699092136870093761401803 107548638205305140642102705)
          ·
            refine ⟨80661478653978855481577029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107548638205305140642102705 80661478653978855481577029)
            ·
              refine ⟨15124027247621035402795693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80661478653978855481577029 15124027247621035402795693)
              ·
                refine ⟨5671510217857888276048385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15124027247621035402795693 5671510217857888276048385)
                ·
                  refine ⟨4253632663393416207036289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671510217857888276048385 4253632663393416207036289)
                  ·
                    refine ⟨3190224497545062155277217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4253632663393416207036289 3190224497545062155277217)
                    ·
                      refine ⟨2392668373158796616457913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190224497545062155277217 2392668373158796616457913)
                      ·
                        rfl

theorem cell23_4659705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_4659705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659705 prefixEnd_4659705 := by exact prefixLift 4659705
  have htrace : WordTrace (prefixWord ++ tailWord_4659705) baseStart_4659705 baseEnd_4659705 := by
    simpa [prefixWord, tailWord_4659705, baseEnd_4659705] using wordTrace_append hprefix tailTrace_4659705
  have hstable : (prefixWord ++ tailWord_4659705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659705).length < 2 ^ (prefixWord ++ tailWord_4659705).sum := by decide
  have hdescent : baseEnd_4659705 < baseStart_4659705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659761 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_4659761 : Nat := 118140960795 + 4659761 * 2 ^ 59
def prefixEnd_4659761 : Nat := 4983230072969 + 3 ^ 40 * 4659761 * 2
def baseEnd_4659761 : Nat := 2392697128075448397357655

theorem tailTrace_4659761 : CollatzResearch.WordTrace tailWord_4659761 prefixEnd_4659761 2392697128075448397357655 := by
  unfold tailWord_4659761
  simp only [CollatzResearch.WordTrace]
  refine ⟨169955446071489195665139137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113303630714326130443426091 169955446071489195665139137)
  ·
    refine ⟨127466584553616896748854353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169955446071489195665139137 127466584553616896748854353)
    ·
      refine ⟨95599938415212672561640765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127466584553616896748854353 95599938415212672561640765)
      ·
        refine ⟨35849976905704752210615287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95599938415212672561640765 35849976905704752210615287)
        ·
          refine ⟨53774965358557128315922931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35849976905704752210615287 53774965358557128315922931)
          ·
            refine ⟨80662448037835692473884397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53774965358557128315922931 80662448037835692473884397)
            ·
              refine ⟨30248418014188384677706649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80662448037835692473884397 30248418014188384677706649)
              ·
                refine ⟨22686313510641288508279987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30248418014188384677706649 22686313510641288508279987)
                ·
                  refine ⟨34029470265961932762419981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22686313510641288508279987 34029470265961932762419981)
                  ·
                    refine ⟨12761051349735724785907493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34029470265961932762419981 12761051349735724785907493)
                    ·
                      refine ⟨2392697128075448397357655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12761051349735724785907493 2392697128075448397357655)
                      ·
                        rfl

theorem cell23_4659761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_4659761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659761 prefixEnd_4659761 := by exact prefixLift 4659761
  have htrace : WordTrace (prefixWord ++ tailWord_4659761) baseStart_4659761 baseEnd_4659761 := by
    simpa [prefixWord, tailWord_4659761, baseEnd_4659761] using wordTrace_append hprefix tailTrace_4659761
  have hstable : (prefixWord ++ tailWord_4659761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659761).length < 2 ^ (prefixWord ++ tailWord_4659761).sum := by decide
  have hdescent : baseEnd_4659761 < baseStart_4659761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659771 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 9, 4]
def baseStart_4659771 : Nat := 118140960795 + 4659771 * 2 ^ 59
def prefixEnd_4659771 : Nat := 4983230072969 + 3 ^ 40 * 4659771 * 2
def baseEnd_4659771 : Nat := 797567420960664452744203

theorem tailTrace_4659771 : CollatzResearch.WordTrace tailWord_4659771 prefixEnd_4659771 797567420960664452744203 := by
  unfold tailWord_4659771
  simp only [CollatzResearch.WordTrace]
  refine ⟨169955810801452967373003167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113303873867635311582002111 169955810801452967373003167)
  ·
    refine ⟨254933716202179451059504751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169955810801452967373003167 254933716202179451059504751)
    ·
      refine ⟨382400574303269176589257127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254933716202179451059504751 382400574303269176589257127)
      ·
        refine ⟨573600861454903764883885691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382400574303269176589257127 573600861454903764883885691)
        ·
          refine ⟨860401292182355647325828537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573600861454903764883885691 860401292182355647325828537)
          ·
            refine ⟨645300969136766735494371403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860401292182355647325828537 645300969136766735494371403)
            ·
              refine ⟨967951453705150103241557105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645300969136766735494371403 967951453705150103241557105)
              ·
                refine ⟨725963590278862577431167829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967951453705150103241557105 725963590278862577431167829)
                ·
                  refine ⟨4253692911790210414635749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 725963590278862577431167829 4253692911790210414635749)
                  ·
                    refine ⟨797567420960664452744203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4253692911790210414635749 797567420960664452744203)
                    ·
                      rfl

theorem cell23_4659771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 4].length) (baseStart_4659771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659771 prefixEnd_4659771 := by exact prefixLift 4659771
  have htrace : WordTrace (prefixWord ++ tailWord_4659771) baseStart_4659771 baseEnd_4659771 := by
    simpa [prefixWord, tailWord_4659771, baseEnd_4659771] using wordTrace_append hprefix tailTrace_4659771
  have hstable : (prefixWord ++ tailWord_4659771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659771).length < 2 ^ (prefixWord ++ tailWord_4659771).sum := by decide
  have hdescent : baseEnd_4659771 < baseStart_4659771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659818 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_4659818 : Nat := 118140960795 + 4659818 * 2 ^ 59
def prefixEnd_4659818 : Nat := 4983230072969 + 3 ^ 40 * 4659818 * 2
def baseEnd_4659818 : Nat := 265858488496972741593877

theorem tailTrace_4659818 : CollatzResearch.WordTrace tailWord_4659818 prefixEnd_4659818 265858488496972741593877 := by
  unfold tailWord_4659818
  simp only [CollatzResearch.WordTrace]
  refine ⟨42489381258070673599991027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113305016688188462933309405 42489381258070673599991027)
  ·
    refine ⟨63734071887106010399986541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42489381258070673599991027 63734071887106010399986541)
    ·
      refine ⟨23900276957664753899994953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63734071887106010399986541 23900276957664753899994953)
      ·
        refine ⟨17925207718248565424996215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23900276957664753899994953 17925207718248565424996215)
        ·
          refine ⟨26887811577372848137494323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17925207718248565424996215 26887811577372848137494323)
          ·
            refine ⟨40331717366059272206241485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26887811577372848137494323 40331717366059272206241485)
            ·
              refine ⟨15124394012272227077340557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40331717366059272206241485 15124394012272227077340557)
              ·
                refine ⟨5671647754602085154002709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15124394012272227077340557 5671647754602085154002709)
                ·
                  refine ⟨265858488496972741593877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5671647754602085154002709 265858488496972741593877)
                  ·
                    rfl

theorem cell23_4659818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_4659818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659818 prefixEnd_4659818 := by exact prefixLift 4659818
  have htrace : WordTrace (prefixWord ++ tailWord_4659818) baseStart_4659818 baseEnd_4659818 := by
    simpa [prefixWord, tailWord_4659818, baseEnd_4659818] using wordTrace_append hprefix tailTrace_4659818
  have hstable : (prefixWord ++ tailWord_4659818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659818).length < 2 ^ (prefixWord ++ tailWord_4659818).sum := by decide
  have hdescent : baseEnd_4659818 < baseStart_4659818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659879 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4659879 : Nat := 118140960795 + 4659879 * 2 ^ 59
def prefixEnd_4659879 : Nat := 4983230072969 + 3 ^ 40 * 4659879 * 2
def baseEnd_4659879 : Nat := 2392757718792678935682113

theorem tailTrace_4659879 : CollatzResearch.WordTrace tailWord_4659879 prefixEnd_4659879 2392757718792678935682113 := by
  unfold tailWord_4659879
  simp only [CollatzResearch.WordTrace]
  refine ⟨169959749885061701817934691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113306499923374467878623127 169959749885061701817934691)
  ·
    refine ⟨254939624827592552726902037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169959749885061701817934691 254939624827592552726902037)
    ·
      refine ⟨11950294913793400909073533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 254939624827592552726902037 11950294913793400909073533)
      ·
        refine ⟨4481360592672525340902575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11950294913793400909073533 4481360592672525340902575)
        ·
          refine ⟨6722040889008788011353863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481360592672525340902575 6722040889008788011353863)
          ·
            refine ⟨10083061333513182017030795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722040889008788011353863 10083061333513182017030795)
            ·
              refine ⟨15124592000269773025546193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10083061333513182017030795 15124592000269773025546193)
              ·
                refine ⟨11343444000202329769159645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15124592000269773025546193 11343444000202329769159645)
                ·
                  refine ⟨4253791500075873663434867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11343444000202329769159645 4253791500075873663434867)
                  ·
                    refine ⟨6380687250113810495152301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253791500075873663434867 6380687250113810495152301)
                    ·
                      refine ⟨2392757718792678935682113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6380687250113810495152301 2392757718792678935682113)
                      ·
                        rfl

theorem cell23_4659879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4659879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659879 prefixEnd_4659879 := by exact prefixLift 4659879
  have htrace : WordTrace (prefixWord ++ tailWord_4659879) baseStart_4659879 baseEnd_4659879 := by
    simpa [prefixWord, tailWord_4659879, baseEnd_4659879] using wordTrace_append hprefix tailTrace_4659879
  have hstable : (prefixWord ++ tailWord_4659879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659879).length < 2 ^ (prefixWord ++ tailWord_4659879).sum := by decide
  have hdescent : baseEnd_4659879 < baseStart_4659879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659885 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_4659885 : Nat := 118140960795 + 4659885 * 2 ^ 59
def prefixEnd_4659885 : Nat := 4983230072969 + 3 ^ 40 * 4659885 * 2
def baseEnd_4659885 : Nat := 2392760799676605912207085

theorem tailTrace_4659885 : CollatzResearch.WordTrace tailWord_4659885 prefixEnd_4659885 2392760799676605912207085 := by
  unfold tailWord_4659885
  simp only [CollatzResearch.WordTrace]
  refine ⟨169959968723039964842653109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113306645815359976561768739 169959968723039964842653109)
  ·
    refine ⟨15933747067784996703998729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169959968723039964842653109 15933747067784996703998729)
    ·
      refine ⟨11950310300838747527999047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15933747067784996703998729 11950310300838747527999047)
      ·
        refine ⟨17925465451258121291998571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11950310300838747527999047 17925465451258121291998571)
        ·
          refine ⟨26888198176887181937997857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17925465451258121291998571 26888198176887181937997857)
          ·
            refine ⟨20166148632665386453498393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26888198176887181937997857 20166148632665386453498393)
            ·
              refine ⟨15124611474499039840123795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20166148632665386453498393 15124611474499039840123795)
              ·
                refine ⟨22686917211748559760185693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15124611474499039840123795 22686917211748559760185693)
                ·
                  refine ⟨8507593954405709910069635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22686917211748559760185693 8507593954405709910069635)
                  ·
                    refine ⟨12761390931608564865104453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8507593954405709910069635 12761390931608564865104453)
                    ·
                      refine ⟨2392760799676605912207085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12761390931608564865104453 2392760799676605912207085)
                      ·
                        rfl

theorem cell23_4659885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_4659885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659885 prefixEnd_4659885 := by exact prefixLift 4659885
  have htrace : WordTrace (prefixWord ++ tailWord_4659885) baseStart_4659885 baseEnd_4659885 := by
    simpa [prefixWord, tailWord_4659885, baseEnd_4659885] using wordTrace_append hprefix tailTrace_4659885
  have hstable : (prefixWord ++ tailWord_4659885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659885).length < 2 ^ (prefixWord ++ tailWord_4659885).sum := by decide
  have hdescent : baseEnd_4659885 < baseStart_4659885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659898 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_4659898 : Nat := 118140960795 + 4659898 * 2 ^ 59
def prefixEnd_4659898 : Nat := 4983230072969 + 3 ^ 40 * 4659898 * 2
def baseEnd_4659898 : Nat := 2392767474925114361344525

theorem tailTrace_4659898 : CollatzResearch.WordTrace tailWord_4659898 prefixEnd_4659898 2392767474925114361344525 := by
  unfold tailWord_4659898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42490110717998217015719087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113306961914661912041917565 42490110717998217015719087)
  ·
    refine ⟨63735166076997325523578631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42490110717998217015719087 63735166076997325523578631)
    ·
      refine ⟨95602749115495988285367947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63735166076997325523578631 95602749115495988285367947)
      ·
        refine ⟨143404123673243982428051921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95602749115495988285367947 143404123673243982428051921)
        ·
          refine ⟨107553092754932986821038941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143404123673243982428051921 107553092754932986821038941)
          ·
            refine ⟨40332409783099870057889603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107553092754932986821038941 40332409783099870057889603)
            ·
              refine ⟨60498614674649805086834405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40332409783099870057889603 60498614674649805086834405)
              ·
                refine ⟨11343490251496838453781451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60498614674649805086834405 11343490251496838453781451)
                ·
                  refine ⟨17015235377245257680672177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11343490251496838453781451 17015235377245257680672177)
                  ·
                    refine ⟨12761426532933943260504133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17015235377245257680672177 12761426532933943260504133)
                    ·
                      refine ⟨2392767474925114361344525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12761426532933943260504133 2392767474925114361344525)
                      ·
                        rfl

theorem cell23_4659898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_4659898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659898 prefixEnd_4659898 := by exact prefixLift 4659898
  have htrace : WordTrace (prefixWord ++ tailWord_4659898) baseStart_4659898 baseEnd_4659898 := by
    simpa [prefixWord, tailWord_4659898, baseEnd_4659898] using wordTrace_append hprefix tailTrace_4659898
  have hstable : (prefixWord ++ tailWord_4659898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659898).length < 2 ^ (prefixWord ++ tailWord_4659898).sum := by decide
  have hdescent : baseEnd_4659898 < baseStart_4659898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659902 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_4659902 : Nat := 118140960795 + 4659902 * 2 ^ 59
def prefixEnd_4659902 : Nat := 4983230072969 + 3 ^ 40 * 4659902 * 2
def baseEnd_4659902 : Nat := 2392769528847732345694507

theorem tailTrace_4659902 : CollatzResearch.WordTrace tailWord_4659902 prefixEnd_4659902 2392769528847732345694507 := by
  unfold tailWord_4659902
  simp only [CollatzResearch.WordTrace]
  refine ⟨21245073595497297093252745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113307059175985584497347973 21245073595497297093252745)
  ·
    refine ⟨15933805196622972819939559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21245073595497297093252745 15933805196622972819939559)
    ·
      refine ⟨23900707794934459229909339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15933805196622972819939559 23900707794934459229909339)
      ·
        refine ⟨35851061692401688844864009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23900707794934459229909339 35851061692401688844864009)
        ·
          refine ⟨26888296269301266633648007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35851061692401688844864009 26888296269301266633648007)
          ·
            refine ⟨40332444403951899950472011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26888296269301266633648007 40332444403951899950472011)
            ·
              refine ⟨60498666605927849925708017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40332444403951899950472011 60498666605927849925708017)
              ·
                refine ⟨45373999954445887444281013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60498666605927849925708017 45373999954445887444281013)
                ·
                  refine ⟨4253812495729301947901345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45373999954445887444281013 4253812495729301947901345)
                  ·
                    refine ⟨3190359371796976460926009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4253812495729301947901345 3190359371796976460926009)
                    ·
                      refine ⟨2392769528847732345694507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190359371796976460926009 2392769528847732345694507)
                      ·
                        rfl

theorem cell23_4659902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_4659902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659902 prefixEnd_4659902 := by exact prefixLift 4659902
  have htrace : WordTrace (prefixWord ++ tailWord_4659902) baseStart_4659902 baseEnd_4659902 := by
    simpa [prefixWord, tailWord_4659902, baseEnd_4659902] using wordTrace_append hprefix tailTrace_4659902
  have hstable : (prefixWord ++ tailWord_4659902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659902).length < 2 ^ (prefixWord ++ tailWord_4659902).sum := by decide
  have hdescent : baseEnd_4659902 < baseStart_4659902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659908 : List Nat := [2, 3, 3, 1, 1, 3, 10]
def baseStart_4659908 : Nat := 118140960795 + 4659908 * 2 ^ 59
def prefixEnd_4659908 : Nat := 4983230072969 + 3 ^ 40 * 4659908 * 2
def baseEnd_4659908 : Nat := 29540402589279744718759

theorem tailTrace_4659908 : CollatzResearch.WordTrace tailWord_4659908 prefixEnd_4659908 29540402589279744718759 := by
  unfold tailWord_4659908
  simp only [CollatzResearch.WordTrace]
  refine ⟨84980403800978319885370189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113307205067971093180493585 84980403800978319885370189)
  ·
    refine ⟨31867651425366869957013821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84980403800978319885370189 31867651425366869957013821)
    ·
      refine ⟨11950369284512576233880183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31867651425366869957013821 11950369284512576233880183)
      ·
        refine ⟨17925553926768864350820275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11950369284512576233880183 17925553926768864350820275)
        ·
          refine ⟨26888330890153296526230413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17925553926768864350820275 26888330890153296526230413)
          ·
            refine ⟨10083124083807486197336405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26888330890153296526230413 10083124083807486197336405)
            ·
              refine ⟨29540402589279744718759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10083124083807486197336405 29540402589279744718759)
              ·
                rfl

theorem cell23_4659908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 10].length) (baseStart_4659908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659908 prefixEnd_4659908 := by exact prefixLift 4659908
  have htrace : WordTrace (prefixWord ++ tailWord_4659908) baseStart_4659908 baseEnd_4659908 := by
    simpa [prefixWord, tailWord_4659908, baseEnd_4659908] using wordTrace_append hprefix tailTrace_4659908
  have hstable : (prefixWord ++ tailWord_4659908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659908).length < 2 ^ (prefixWord ++ tailWord_4659908).sum := by decide
  have hdescent : baseEnd_4659908 < baseStart_4659908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659912 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 2, 4]
def baseStart_4659912 : Nat := 118140960795 + 4659912 * 2 ^ 59
def prefixEnd_4659912 : Nat := 4983230072969 + 3 ^ 40 * 4659912 * 2
def baseEnd_4659912 : Nat := 797591554551425768856487

theorem tailTrace_4659912 : CollatzResearch.WordTrace tailWord_4659912 prefixEnd_4659912 797591554551425768856487 := by
  unfold tailWord_4659912
  simp only [CollatzResearch.WordTrace]
  refine ⟨84980476746971074226942995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113307302329294765635923993 84980476746971074226942995)
  ·
    refine ⟨127470715120456611340414493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84980476746971074226942995 127470715120456611340414493)
    ·
      refine ⟨47801518170171229252655435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127470715120456611340414493 47801518170171229252655435)
      ·
        refine ⟨71702277255256843878983153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47801518170171229252655435 71702277255256843878983153)
        ·
          refine ⟨53776707941442632909237365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71702277255256843878983153 53776707941442632909237365)
          ·
            refine ⟨5041566369510246835241003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53776707941442632909237365 5041566369510246835241003)
            ·
              refine ⟨7562349554265370252861505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041566369510246835241003 7562349554265370252861505)
              ·
                refine ⟨5671762165699027689646129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7562349554265370252861505 5671762165699027689646129)
                ·
                  refine ⟨4253821624274270767234597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671762165699027689646129 4253821624274270767234597)
                  ·
                    refine ⟨797591554551425768856487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4253821624274270767234597 797591554551425768856487)
                    ·
                      rfl

theorem cell23_4659912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_4659912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659912 prefixEnd_4659912 := by exact prefixLift 4659912
  have htrace : WordTrace (prefixWord ++ tailWord_4659912) baseStart_4659912 baseEnd_4659912 := by
    simpa [prefixWord, tailWord_4659912, baseEnd_4659912] using wordTrace_append hprefix tailTrace_4659912
  have hstable : (prefixWord ++ tailWord_4659912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659912).length < 2 ^ (prefixWord ++ tailWord_4659912).sum := by decide
  have hdescent : baseEnd_4659912 < baseStart_4659912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659932 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4659932 : Nat := 118140960795 + 4659932 * 2 ^ 59
def prefixEnd_4659932 : Nat := 4983230072969 + 3 ^ 40 * 4659932 * 2
def baseEnd_4659932 : Nat := 2392784933267367228319369

theorem tailTrace_4659932 : CollatzResearch.WordTrace tailWord_4659932 prefixEnd_4659932 2392784933267367228319369 := by
  unfold tailWord_4659932
  simp only [CollatzResearch.WordTrace]
  refine ⟨84980841476934845934807025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113307788635913127913076033 84980841476934845934807025)
  ·
    refine ⟨63735631107701134451105269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84980841476934845934807025 63735631107701134451105269)
    ·
      refine ⟨5975215416346981354791119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63735631107701134451105269 5975215416346981354791119)
      ·
        refine ⟨8962823124520472032186679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5975215416346981354791119 8962823124520472032186679)
        ·
          refine ⟨13444234686780708048280019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8962823124520472032186679 13444234686780708048280019)
          ·
            refine ⟨20166352030171062072420029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13444234686780708048280019 20166352030171062072420029)
            ·
              refine ⟨7562382011314148277157511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20166352030171062072420029 7562382011314148277157511)
              ·
                refine ⟨11343573016971222415736267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7562382011314148277157511 11343573016971222415736267)
                ·
                  refine ⟨17015359525456833623604401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11343573016971222415736267 17015359525456833623604401)
                  ·
                    refine ⟨12761519644092625217703301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17015359525456833623604401 12761519644092625217703301)
                    ·
                      refine ⟨2392784933267367228319369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12761519644092625217703301 2392784933267367228319369)
                      ·
                        rfl

theorem cell23_4659932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4659932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659932 prefixEnd_4659932 := by exact prefixLift 4659932
  have htrace : WordTrace (prefixWord ++ tailWord_4659932) baseStart_4659932 baseEnd_4659932 := by
    simpa [prefixWord, tailWord_4659932, baseEnd_4659932] using wordTrace_append hprefix tailTrace_4659932
  have hstable : (prefixWord ++ tailWord_4659932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659932).length < 2 ^ (prefixWord ++ tailWord_4659932).sum := by decide
  have hdescent : baseEnd_4659932 < baseStart_4659932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659935 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_4659935 : Nat := 118140960795 + 4659935 * 2 ^ 59
def prefixEnd_4659935 : Nat := 4983230072969 + 3 ^ 40 * 4659935 * 2
def baseEnd_4659935 : Nat := 2392786473709330716581855

theorem tailTrace_4659935 : CollatzResearch.WordTrace tailWord_4659935 prefixEnd_4659935 2392786473709330716581855 := by
  unfold tailWord_4659935
  simp only [CollatzResearch.WordTrace]
  refine ⟨169961792372858823381973259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113307861581905882254648839 169961792372858823381973259)
  ·
    refine ⟨254942688559288235072959889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169961792372858823381973259 254942688559288235072959889)
    ·
      refine ⟨191207016419466176304719917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254942688559288235072959889 191207016419466176304719917)
      ·
        refine ⟨71702631157299816114269969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191207016419466176304719917 71702631157299816114269969)
        ·
          refine ⟨53776973367974862085702477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71702631157299816114269969 53776973367974862085702477)
          ·
            refine ⟨20166365012990573282138429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53776973367974862085702477 20166365012990573282138429)
            ·
              refine ⟨7562386879871464980801911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20166365012990573282138429 7562386879871464980801911)
              ·
                refine ⟨11343580319807197471202867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7562386879871464980801911 11343580319807197471202867)
                ·
                  refine ⟨17015370479710796206804301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11343580319807197471202867 17015370479710796206804301)
                  ·
                    refine ⟨6380763929891548577551613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17015370479710796206804301 6380763929891548577551613)
                    ·
                      refine ⟨2392786473709330716581855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6380763929891548577551613 2392786473709330716581855)
                      ·
                        rfl

theorem cell23_4659935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_4659935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659935 prefixEnd_4659935 := by exact prefixLift 4659935
  have htrace : WordTrace (prefixWord ++ tailWord_4659935) baseStart_4659935 baseEnd_4659935 := by
    simpa [prefixWord, tailWord_4659935, baseEnd_4659935] using wordTrace_append hprefix tailTrace_4659935
  have hstable : (prefixWord ++ tailWord_4659935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659935).length < 2 ^ (prefixWord ++ tailWord_4659935).sum := by decide
  have hdescent : baseEnd_4659935 < baseStart_4659935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659945 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 3, 3, 2]
def baseStart_4659945 : Nat := 118140960795 + 4659945 * 2 ^ 59
def prefixEnd_4659945 : Nat := 4983230072969 + 3 ^ 40 * 4659945 * 2
def baseEnd_4659945 : Nat := 2392791608515875677456809

theorem tailTrace_4659945 : CollatzResearch.WordTrace tailWord_4659945 prefixEnd_4659945 2392791608515875677456809 := by
  unfold tailWord_4659945
  simp only [CollatzResearch.WordTrace]
  refine ⟨169962157102822595089837289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113308104735215063393224859 169962157102822595089837289)
  ·
    refine ⟨127471617827116946317377967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169962157102822595089837289 127471617827116946317377967)
    ·
      refine ⟨191207426740675419476066951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127471617827116946317377967 191207426740675419476066951)
      ·
        refine ⟨286811140111013129214100427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191207426740675419476066951 286811140111013129214100427)
        ·
          refine ⟨430216710166519693821150641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286811140111013129214100427 430216710166519693821150641)
          ·
            refine ⟨322662532624889770365862981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430216710166519693821150641 322662532624889770365862981)
            ·
              refine ⟨60499224867166831943599309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 322662532624889770365862981 60499224867166831943599309)
              ·
                refine ⟨22687209325187561978849741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60499224867166831943599309 22687209325187561978849741)
                ·
                  refine ⟨8507703496945335742068653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22687209325187561978849741 8507703496945335742068653)
                  ·
                    refine ⟨3190388811354500903275745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8507703496945335742068653 3190388811354500903275745)
                    ·
                      refine ⟨2392791608515875677456809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190388811354500903275745 2392791608515875677456809)
                      ·
                        rfl

theorem cell23_4659945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 3, 2].length) (baseStart_4659945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659945 prefixEnd_4659945 := by exact prefixLift 4659945
  have htrace : WordTrace (prefixWord ++ tailWord_4659945) baseStart_4659945 baseEnd_4659945 := by
    simpa [prefixWord, tailWord_4659945, baseEnd_4659945] using wordTrace_append hprefix tailTrace_4659945
  have hstable : (prefixWord ++ tailWord_4659945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659945).length < 2 ^ (prefixWord ++ tailWord_4659945).sum := by decide
  have hdescent : baseEnd_4659945 < baseStart_4659945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659962 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2]
def baseStart_4659962 : Nat := 118140960795 + 4659962 * 2 ^ 59
def prefixEnd_4659962 : Nat := 4983230072969 + 3 ^ 40 * 4659962 * 2
def baseEnd_4659962 : Nat := 2392800337687002110944231

theorem tailTrace_4659962 : CollatzResearch.WordTrace tailWord_4659962 prefixEnd_4659962 2392800337687002110944231 := by
  unfold tailWord_4659962
  simp only [CollatzResearch.WordTrace]
  refine ⟨42490694285940251748301535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113308518095840671328804093 42490694285940251748301535)
  ·
    refine ⟨63736041428910377622452303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42490694285940251748301535 63736041428910377622452303)
    ·
      refine ⟨95604062143365566433678455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63736041428910377622452303 95604062143365566433678455)
      ·
        refine ⟨143406093215048349650517683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95604062143365566433678455 143406093215048349650517683)
        ·
          refine ⟨215109139822572524475776525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143406093215048349650517683 215109139822572524475776525)
          ·
            refine ⟨80665927433464696678416197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215109139822572524475776525 80665927433464696678416197)
            ·
              refine ⟨15124861393774630627203037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80665927433464696678416197 15124861393774630627203037)
              ·
                refine ⟨5671823022665486485201139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15124861393774630627203037 5671823022665486485201139)
                ·
                  refine ⟨8507734533998229727801709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671823022665486485201139 8507734533998229727801709)
                  ·
                    refine ⟨3190400450249336147925641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8507734533998229727801709 3190400450249336147925641)
                    ·
                      refine ⟨2392800337687002110944231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190400450249336147925641 2392800337687002110944231)
                      ·
                        rfl

theorem cell23_4659962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_4659962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659962 prefixEnd_4659962 := by exact prefixLift 4659962
  have htrace : WordTrace (prefixWord ++ tailWord_4659962) baseStart_4659962 baseEnd_4659962 := by
    simpa [prefixWord, tailWord_4659962, baseEnd_4659962] using wordTrace_append hprefix tailTrace_4659962
  have hstable : (prefixWord ++ tailWord_4659962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659962).length < 2 ^ (prefixWord ++ tailWord_4659962).sum := by decide
  have hdescent : baseEnd_4659962 < baseStart_4659962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659978 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4659978 : Nat := 118140960795 + 4659978 * 2 ^ 59
def prefixEnd_4659978 : Nat := 4983230072969 + 3 ^ 40 * 4659978 * 2
def baseEnd_4659978 : Nat := 2392808553377474048344157

theorem tailTrace_4659978 : CollatzResearch.WordTrace tailWord_4659978 prefixEnd_4659978 2392808553377474048344157 := by
  unfold tailWord_4659978
  simp only [CollatzResearch.WordTrace]
  refine ⟨42490840177925760431447147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113308907141135361150525725 42490840177925760431447147)
  ·
    refine ⟨63736260266888640647170721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42490840177925760431447147 63736260266888640647170721)
    ·
      refine ⟨47802195200166480485378041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63736260266888640647170721 47802195200166480485378041)
      ·
        refine ⟨35851646400124860364033531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47802195200166480485378041 35851646400124860364033531)
        ·
          refine ⟨53777469600187290546050297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35851646400124860364033531 53777469600187290546050297)
          ·
            refine ⟨40333102200140467909537723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53777469600187290546050297 40333102200140467909537723)
            ·
              refine ⟨60499653300210701864306585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40333102200140467909537723 60499653300210701864306585)
              ·
                refine ⟨45374739975158026398229939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60499653300210701864306585 45374739975158026398229939)
                ·
                  refine ⟨68062109962737039597344909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45374739975158026398229939 68062109962737039597344909)
                  ·
                    refine ⟨25523291236026389849004341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68062109962737039597344909 25523291236026389849004341)
                    ·
                      refine ⟨2392808553377474048344157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25523291236026389849004341 2392808553377474048344157)
                      ·
                        rfl

theorem cell23_4659978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4659978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659978 prefixEnd_4659978 := by exact prefixLift 4659978
  have htrace : WordTrace (prefixWord ++ tailWord_4659978) baseStart_4659978 baseEnd_4659978 := by
    simpa [prefixWord, tailWord_4659978, baseEnd_4659978] using wordTrace_append hprefix tailTrace_4659978
  have hstable : (prefixWord ++ tailWord_4659978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659978).length < 2 ^ (prefixWord ++ tailWord_4659978).sum := by decide
  have hdescent : baseEnd_4659978 < baseStart_4659978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4659986 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4659986 : Nat := 118140960795 + 4659986 * 2 ^ 59
def prefixEnd_4659986 : Nat := 4983230072969 + 3 ^ 40 * 4659986 * 2
def baseEnd_4659986 : Nat := 2392812661222710017044121

theorem tailTrace_4659986 : CollatzResearch.WordTrace tailWord_4659986 prefixEnd_4659986 2392812661222710017044121 := by
  unfold tailWord_4659986
  simp only [CollatzResearch.WordTrace]
  refine ⟨42490913123918514773019953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113309101663782706061386541 42490913123918514773019953)
  ·
    refine ⟨31868184842938886079764965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42490913123918514773019953 31868184842938886079764965)
    ·
      refine ⟨5975284658051041139955931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31868184842938886079764965 5975284658051041139955931)
      ·
        refine ⟨8962926987076561709933897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5975284658051041139955931 8962926987076561709933897)
        ·
          refine ⟨6722195240307421282450423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8962926987076561709933897 6722195240307421282450423)
          ·
            refine ⟨10083292860461131923675635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722195240307421282450423 10083292860461131923675635)
            ·
              refine ⟨15124939290691697885513453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10083292860461131923675635 15124939290691697885513453)
              ·
                refine ⟨5671852234009386707067545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15124939290691697885513453 5671852234009386707067545)
                ·
                  refine ⟨4253889175507040030300659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671852234009386707067545 4253889175507040030300659)
                  ·
                    refine ⟨6380833763260560045450989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253889175507040030300659 6380833763260560045450989)
                    ·
                      refine ⟨2392812661222710017044121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6380833763260560045450989 2392812661222710017044121)
                      ·
                        rfl

theorem cell23_4659986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4659986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4659986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4659986 prefixEnd_4659986 := by exact prefixLift 4659986
  have htrace : WordTrace (prefixWord ++ tailWord_4659986) baseStart_4659986 baseEnd_4659986 := by
    simpa [prefixWord, tailWord_4659986, baseEnd_4659986] using wordTrace_append hprefix tailTrace_4659986
  have hstable : (prefixWord ++ tailWord_4659986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4659986).length < 2 ^ (prefixWord ++ tailWord_4659986).sum := by decide
  have hdescent : baseEnd_4659986 < baseStart_4659986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4659986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660026 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2]
def baseStart_4660026 : Nat := 118140960795 + 4660026 * 2 ^ 59
def prefixEnd_4660026 : Nat := 4983230072969 + 3 ^ 40 * 4660026 * 2
def baseEnd_4660026 : Nat := 2392833200448889860543937

theorem tailTrace_4660026 : CollatzResearch.WordTrace tailWord_4660026 prefixEnd_4660026 2392833200448889860543937 := by
  unfold tailWord_4660026
  simp only [CollatzResearch.WordTrace]
  refine ⟨42491277853882286480883983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113310074277019430615690621 42491277853882286480883983)
  ·
    refine ⟨63736916780823429721325975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42491277853882286480883983 63736916780823429721325975)
    ·
      refine ⟨95605375171235144581988963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63736916780823429721325975 95605375171235144581988963)
      ·
        refine ⟨143408062756852716872983445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95605375171235144581988963 143408062756852716872983445)
        ·
          refine ⟨6722252941727471103421099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143408062756852716872983445 6722252941727471103421099)
          ·
            refine ⟨10083379412591206655131649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722252941727471103421099 10083379412591206655131649)
            ·
              refine ⟨7562534559443404991348737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10083379412591206655131649 7562534559443404991348737)
              ·
                refine ⟨5671900919582553743511553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7562534559443404991348737 5671900919582553743511553)
                ·
                  refine ⟨4253925689686915307633665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671900919582553743511553 4253925689686915307633665)
                  ·
                    refine ⟨3190444267265186480725249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4253925689686915307633665 3190444267265186480725249)
                    ·
                      refine ⟨2392833200448889860543937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190444267265186480725249 2392833200448889860543937)
                      ·
                        rfl

theorem cell23_4660026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_4660026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660026 prefixEnd_4660026 := by exact prefixLift 4660026
  have htrace : WordTrace (prefixWord ++ tailWord_4660026) baseStart_4660026 baseEnd_4660026 := by
    simpa [prefixWord, tailWord_4660026, baseEnd_4660026] using wordTrace_append hprefix tailTrace_4660026
  have hstable : (prefixWord ++ tailWord_4660026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660026).length < 2 ^ (prefixWord ++ tailWord_4660026).sum := by decide
  have hdescent : baseEnd_4660026 < baseStart_4660026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660028 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_4660028 : Nat := 118140960795 + 4660028 * 2 ^ 59
def prefixEnd_4660028 : Nat := 4983230072969 + 3 ^ 40 * 4660028 * 2
def baseEnd_4660028 : Nat := 797611409136732950906309

theorem tailTrace_4660028 : CollatzResearch.WordTrace tailWord_4660028 prefixEnd_4660028 797611409136732950906309 := by
  unfold tailWord_4660028
  simp only [CollatzResearch.WordTrace]
  refine ⟨84982592180760950132554369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113310122907681266843405825 84982592180760950132554369)
  ·
    refine ⟨63736944135570712599415777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84982592180760950132554369 63736944135570712599415777)
    ·
      refine ⟨47802708101678034449561833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63736944135570712599415777 47802708101678034449561833)
      ·
        refine ⟨35852031076258525837171375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47802708101678034449561833 35852031076258525837171375)
        ·
          refine ⟨53778046614387788755757063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35852031076258525837171375 53778046614387788755757063)
          ·
            refine ⟨80667069921581683133635595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53778046614387788755757063 80667069921581683133635595)
            ·
              refine ⟨121000604882372524700453393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80667069921581683133635595 121000604882372524700453393)
              ·
                refine ⟨90750453661779393525340045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121000604882372524700453393 90750453661779393525340045)
                ·
                  refine ⟨34031420123167272572002517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90750453661779393525340045 34031420123167272572002517)
                  ·
                    refine ⟨797611409136732950906309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34031420123167272572002517 797611409136732950906309)
                    ·
                      rfl

theorem cell23_4660028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_4660028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660028 prefixEnd_4660028 := by exact prefixLift 4660028
  have htrace : WordTrace (prefixWord ++ tailWord_4660028) baseStart_4660028 baseEnd_4660028 := by
    simpa [prefixWord, tailWord_4660028, baseEnd_4660028] using wordTrace_append hprefix tailTrace_4660028
  have hstable : (prefixWord ++ tailWord_4660028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660028).length < 2 ^ (prefixWord ++ tailWord_4660028).sum := by decide
  have hdescent : baseEnd_4660028 < baseStart_4660028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660035 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 7, 2]
def baseStart_4660035 : Nat := 118140960795 + 4660035 * 2 ^ 59
def prefixEnd_4660035 : Nat := 4983230072969 + 3 ^ 40 * 4660035 * 2
def baseEnd_4660035 : Nat := 2392837821774780325331395

theorem tailTrace_4660035 : CollatzResearch.WordTrace tailWord_4660035 prefixEnd_4660035 2392837821774780325331395 := by
  unfold tailWord_4660035
  simp only [CollatzResearch.WordTrace]
  refine ⟨169965439672496540460613559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113310293114997693640409039 169965439672496540460613559)
  ·
    refine ⟨254948159508744810690920339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169965439672496540460613559 254948159508744810690920339)
    ·
      refine ⟨382422239263117216036380509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254948159508744810690920339 382422239263117216036380509)
      ·
        refine ⟨143408339723668956013642691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382422239263117216036380509 143408339723668956013642691)
        ·
          refine ⟨215112509585503434020464037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143408339723668956013642691 215112509585503434020464037)
          ·
            refine ⟨40333595547281893878837007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215112509585503434020464037 40333595547281893878837007)
            ·
              refine ⟨60500393320922840818255511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40333595547281893878837007 60500393320922840818255511)
              ·
                refine ⟨90750589981384261227383267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60500393320922840818255511 90750589981384261227383267)
                ·
                  refine ⟨136125884972076391841074901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90750589981384261227383267 136125884972076391841074901)
                  ·
                    refine ⟨3190450429033040433775193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136125884972076391841074901 3190450429033040433775193)
                    ·
                      refine ⟨2392837821774780325331395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190450429033040433775193 2392837821774780325331395)
                      ·
                        rfl

theorem cell23_4660035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_4660035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660035 prefixEnd_4660035 := by exact prefixLift 4660035
  have htrace : WordTrace (prefixWord ++ tailWord_4660035) baseStart_4660035 baseEnd_4660035 := by
    simpa [prefixWord, tailWord_4660035, baseEnd_4660035] using wordTrace_append hprefix tailTrace_4660035
  have hstable : (prefixWord ++ tailWord_4660035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660035).length < 2 ^ (prefixWord ++ tailWord_4660035).sum := by decide
  have hdescent : baseEnd_4660035 < baseStart_4660035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660065 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_4660065 : Nat := 118140960795 + 4660065 * 2 ^ 59
def prefixEnd_4660065 : Nat := 4983230072969 + 3 ^ 40 * 4660065 * 2
def baseEnd_4660065 : Nat := 2392853226194415207956257

theorem tailTrace_4660065 : CollatzResearch.WordTrace tailWord_4660065 prefixEnd_4660065 2392853226194415207956257 := by
  unfold tailWord_4660065
  simp only [CollatzResearch.WordTrace]
  refine ⟨169966533862387855584205649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113311022574925237056137099 169966533862387855584205649)
  ·
    refine ⟨127474900396790891688154237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169966533862387855584205649 127474900396790891688154237)
    ·
      refine ⟨47803087648796584383057839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127474900396790891688154237 47803087648796584383057839)
      ·
        refine ⟨71704631473194876574586759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47803087648796584383057839 71704631473194876574586759)
        ·
          refine ⟨107556947209792314861880139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71704631473194876574586759 107556947209792314861880139)
          ·
            refine ⟨161335420814688472292820209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107556947209792314861880139 161335420814688472292820209)
            ·
              refine ⟨121001565611016354219615157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161335420814688472292820209 121001565611016354219615157)
              ·
                refine ⟨11343896776032783208088921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121001565611016354219615157 11343896776032783208088921)
                ·
                  refine ⟨8507922582024587406066691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11343896776032783208088921 8507922582024587406066691)
                  ·
                    refine ⟨12761883873036881109100037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8507922582024587406066691 12761883873036881109100037)
                    ·
                      refine ⟨2392853226194415207956257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12761883873036881109100037 2392853226194415207956257)
                      ·
                        rfl

theorem cell23_4660065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_4660065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660065 prefixEnd_4660065 := by exact prefixLift 4660065
  have htrace : WordTrace (prefixWord ++ tailWord_4660065) baseStart_4660065 baseEnd_4660065 := by
    simpa [prefixWord, tailWord_4660065, baseEnd_4660065] using wordTrace_append hprefix tailTrace_4660065
  have hstable : (prefixWord ++ tailWord_4660065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660065).length < 2 ^ (prefixWord ++ tailWord_4660065).sum := by decide
  have hdescent : baseEnd_4660065 < baseStart_4660065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660082 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_4660082 : Nat := 118140960795 + 4660082 * 2 ^ 59
def prefixEnd_4660082 : Nat := 4983230072969 + 3 ^ 40 * 4660082 * 2
def baseEnd_4660082 : Nat := 2392861955365541641443679

theorem tailTrace_4660082 : CollatzResearch.WordTrace tailWord_4660082 prefixEnd_4660082 2392861955365541641443679 := by
  unfold tailWord_4660082
  simp only [CollatzResearch.WordTrace]
  refine ⟨42491788475831566871893625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113311435935550844991716333 42491788475831566871893625)
  ·
    refine ⟨31868841356873675153920219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42491788475831566871893625 31868841356873675153920219)
    ·
      refine ⟨47803262035310512730880329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31868841356873675153920219 47803262035310512730880329)
      ·
        refine ⟨35852446526482884548160247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47803262035310512730880329 35852446526482884548160247)
        ·
          refine ⟨53778669789724326822240371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35852446526482884548160247 53778669789724326822240371)
          ·
            refine ⟨80668004684586490233360557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53778669789724326822240371 80668004684586490233360557)
            ·
              refine ⟨30250501756719933837510209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80668004684586490233360557 30250501756719933837510209)
              ·
                refine ⟨22687876317539950378132657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30250501756719933837510209 22687876317539950378132657)
                ·
                  refine ⟨17015907238154962783599493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22687876317539950378132657 17015907238154962783599493)
                  ·
                    refine ⟨3190482607154055521924905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17015907238154962783599493 3190482607154055521924905)
                    ·
                      refine ⟨2392861955365541641443679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190482607154055521924905 2392861955365541641443679)
                      ·
                        rfl

theorem cell23_4660082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_4660082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660082 prefixEnd_4660082 := by exact prefixLift 4660082
  have htrace : WordTrace (prefixWord ++ tailWord_4660082) baseStart_4660082 baseEnd_4660082 := by
    simpa [prefixWord, tailWord_4660082, baseEnd_4660082] using wordTrace_append hprefix tailTrace_4660082
  have hstable : (prefixWord ++ tailWord_4660082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660082).length < 2 ^ (prefixWord ++ tailWord_4660082).sum := by decide
  have hdescent : baseEnd_4660082 < baseStart_4660082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660172 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4660172 : Nat := 118140960795 + 4660172 * 2 ^ 59
def prefixEnd_4660172 : Nat := 4983230072969 + 3 ^ 40 * 4660172 * 2
def baseEnd_4660172 : Nat := 2392908168624446289318265

theorem tailTrace_4660172 : CollatzResearch.WordTrace tailWord_4660172 prefixEnd_4660172 2392908168624446289318265 := by
  unfold tailWord_4660172
  simp only [CollatzResearch.WordTrace]
  refine ⟨84985218236500106429175385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113313624315333475238900513 84985218236500106429175385)
  ·
    refine ⟨63738913677375079821881539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84985218236500106429175385 63738913677375079821881539)
    ·
      refine ⟨95608370516062619732822309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63738913677375079821881539 95608370516062619732822309)
      ·
        refine ⟨17926569471761741199904183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95608370516062619732822309 17926569471761741199904183)
        ·
          refine ⟨26889854207642611799856275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17926569471761741199904183 26889854207642611799856275)
          ·
            refine ⟨40334781311463917699784413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26889854207642611799856275 40334781311463917699784413)
            ·
              refine ⟨15125542991798969137419155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40334781311463917699784413 15125542991798969137419155)
              ·
                refine ⟨22688314487698453706128733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15125542991798969137419155 22688314487698453706128733)
                ·
                  refine ⟨8508117932886920139798275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22688314487698453706128733 8508117932886920139798275)
                  ·
                    refine ⟨12762176899330380209697413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8508117932886920139798275 12762176899330380209697413)
                    ·
                      refine ⟨2392908168624446289318265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12762176899330380209697413 2392908168624446289318265)
                      ·
                        rfl

theorem cell23_4660172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4660172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660172 prefixEnd_4660172 := by exact prefixLift 4660172
  have htrace : WordTrace (prefixWord ++ tailWord_4660172) baseStart_4660172 baseEnd_4660172 := by
    simpa [prefixWord, tailWord_4660172, baseEnd_4660172] using wordTrace_append hprefix tailTrace_4660172
  have hstable : (prefixWord ++ tailWord_4660172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660172).length < 2 ^ (prefixWord ++ tailWord_4660172).sum := by decide
  have hdescent : baseEnd_4660172 < baseStart_4660172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660199 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 2, 4]
def baseStart_4660199 : Nat := 118140960795 + 4660199 * 2 ^ 59
def prefixEnd_4660199 : Nat := 4983230072969 + 3 ^ 40 * 4660199 * 2
def baseEnd_4660199 : Nat := 797640677534039227893547

theorem tailTrace_4660199 : CollatzResearch.WordTrace tailWord_4660199 prefixEnd_4660199 797640677534039227893547 := by
  unfold tailWord_4660199
  simp only [CollatzResearch.WordTrace]
  refine ⟨169971421243902396469583651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113314280829268264313055767 169971421243902396469583651)
  ·
    refine ⟨254957131865853594704375477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169971421243902396469583651 254957131865853594704375477)
    ·
      refine ⟨23902231112423774503535201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254957131865853594704375477 23902231112423774503535201)
      ·
        refine ⟨17926673334317830877651401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23902231112423774503535201 17926673334317830877651401)
        ·
          refine ⟨13445005000738373158238551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17926673334317830877651401 13445005000738373158238551)
          ·
            refine ⟨20167507501107559737357827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13445005000738373158238551 20167507501107559737357827)
            ·
              refine ⟨30251261251661339606036741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20167507501107559737357827 30251261251661339606036741)
              ·
                refine ⟨5672111484686501176131889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30251261251661339606036741 5672111484686501176131889)
                ·
                  refine ⟨4254083613514875882098917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5672111484686501176131889 4254083613514875882098917)
                  ·
                    refine ⟨797640677534039227893547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4254083613514875882098917 797640677534039227893547)
                    ·
                      rfl

theorem cell23_4660199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_4660199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660199 prefixEnd_4660199 := by exact prefixLift 4660199
  have htrace : WordTrace (prefixWord ++ tailWord_4660199) baseStart_4660199 baseEnd_4660199 := by
    simpa [prefixWord, tailWord_4660199, baseEnd_4660199] using wordTrace_append hprefix tailTrace_4660199
  have hstable : (prefixWord ++ tailWord_4660199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660199).length < 2 ^ (prefixWord ++ tailWord_4660199).sum := by decide
  have hdescent : baseEnd_4660199 < baseStart_4660199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660282 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_4660282 : Nat := 118140960795 + 4660282 * 2 ^ 59
def prefixEnd_4660282 : Nat := 4983230072969 + 3 ^ 40 * 4660282 * 2
def baseEnd_4660282 : Nat := 2392964651496440858942759

theorem tailTrace_4660282 : CollatzResearch.WordTrace tailWord_4660282 prefixEnd_4660282 2392964651496440858942759 := by
  unfold tailWord_4660282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42493612125650425411213775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113316299001734467763236733 42493612125650425411213775)
  ·
    refine ⟨63740418188475638116820663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42493612125650425411213775 63740418188475638116820663)
    ·
      refine ⟨95610627282713457175230995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63740418188475638116820663 95610627282713457175230995)
      ·
        refine ⟨143415940924070185762846493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95610627282713457175230995 143415940924070185762846493)
        ·
          refine ⟨53780977846526319661067435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143415940924070185762846493 53780977846526319661067435)
          ·
            refine ⟨80671466769789479491601153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53780977846526319661067435 80671466769789479491601153)
            ·
              refine ⟨60503600077342109618700865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80671466769789479491601153 60503600077342109618700865)
              ·
                refine ⟨45377700058006582214025649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60503600077342109618700865 45377700058006582214025649)
                ·
                  refine ⟨34033275043504936660519237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45377700058006582214025649 34033275043504936660519237)
                  ·
                    refine ⟨6381239070657175623847357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34033275043504936660519237 6381239070657175623847357)
                    ·
                      refine ⟨2392964651496440858942759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6381239070657175623847357 2392964651496440858942759)
                      ·
                        rfl

theorem cell23_4660282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_4660282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660282 prefixEnd_4660282 := by exact prefixLift 4660282
  have htrace : WordTrace (prefixWord ++ tailWord_4660282) baseStart_4660282 baseEnd_4660282 := by
    simpa [prefixWord, tailWord_4660282, baseEnd_4660282] using wordTrace_append hprefix tailTrace_4660282
  have hstable : (prefixWord ++ tailWord_4660282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660282).length < 2 ^ (prefixWord ++ tailWord_4660282).sum := by decide
  have hdescent : baseEnd_4660282 < baseStart_4660282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660330 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_4660330 : Nat := 118140960795 + 4660330 * 2 ^ 59
def prefixEnd_4660330 : Nat := 4983230072969 + 3 ^ 40 * 4660330 * 2
def baseEnd_4660330 : Nat := 2392989298567856671142539

theorem tailTrace_4660330 : CollatzResearch.WordTrace tailWord_4660330 prefixEnd_4660330 2392989298567856671142539 := by
  unfold tailWord_4660330
  simp only [CollatzResearch.WordTrace]
  refine ⟨42494049801606951460650611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113317466137618537228401629 42494049801606951460650611)
  ·
    refine ⟨63741074702410427190975917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42494049801606951460650611 63741074702410427190975917)
    ·
      refine ⟨23902903013403910196615969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63741074702410427190975917 23902903013403910196615969)
      ·
        refine ⟨17927177260052932647461977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23902903013403910196615969 17927177260052932647461977)
        ·
          refine ⟨13445382945039699485596483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17927177260052932647461977 13445382945039699485596483)
          ·
            refine ⟨20168074417559549228394725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13445382945039699485596483 20168074417559549228394725)
            ·
              refine ⟨3781513953292415480324011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20168074417559549228394725 3781513953292415480324011)
              ·
                refine ⟨5672270929938623220486017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781513953292415480324011 5672270929938623220486017)
                ·
                  refine ⟨4254203197453967415364513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5672270929938623220486017 4254203197453967415364513)
                  ·
                    refine ⟨3190652398090475561523385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4254203197453967415364513 3190652398090475561523385)
                    ·
                      refine ⟨2392989298567856671142539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190652398090475561523385 2392989298567856671142539)
                      ·
                        rfl

theorem cell23_4660330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_4660330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660330 prefixEnd_4660330 := by exact prefixLift 4660330
  have htrace : WordTrace (prefixWord ++ tailWord_4660330) baseStart_4660330 baseEnd_4660330 := by
    simpa [prefixWord, tailWord_4660330, baseEnd_4660330] using wordTrace_append hprefix tailTrace_4660330
  have hstable : (prefixWord ++ tailWord_4660330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660330).length < 2 ^ (prefixWord ++ tailWord_4660330).sum := by decide
  have hdescent : baseEnd_4660330 < baseStart_4660330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660332 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_4660332 : Nat := 118140960795 + 4660332 * 2 ^ 59
def prefixEnd_4660332 : Nat := 4983230072969 + 3 ^ 40 * 4660332 * 2
def baseEnd_4660332 : Nat := 797663441843055221105843

theorem tailTrace_4660332 : CollatzResearch.WordTrace tailWord_4660332 prefixEnd_4660332 797663441843055221105843 := by
  unfold tailWord_4660332
  simp only [CollatzResearch.WordTrace]
  refine ⟨84988136076210280092087625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113317514768280373456116833 84988136076210280092087625)
  ·
    refine ⟨63741102057157710069065719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84988136076210280092087625 63741102057157710069065719)
    ·
      refine ⟨95611653085736565103598579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63741102057157710069065719 95611653085736565103598579)
      ·
        refine ⟨143417479628604847655397869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95611653085736565103598579 143417479628604847655397869)
        ·
          refine ⟨53781554860726817870774201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143417479628604847655397869 53781554860726817870774201)
          ·
            refine ⟨40336166145545113403080651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53781554860726817870774201 40336166145545113403080651)
            ·
              refine ⟨60504249218317670104620977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40336166145545113403080651 60504249218317670104620977)
              ·
                refine ⟨45378186913738252578465733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60504249218317670104620977 45378186913738252578465733)
                ·
                  refine ⟨8508410046325922358462325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45378186913738252578465733 8508410046325922358462325)
                  ·
                    refine ⟨797663441843055221105843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8508410046325922358462325 797663441843055221105843)
                    ·
                      rfl

theorem cell23_4660332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_4660332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660332 prefixEnd_4660332 := by exact prefixLift 4660332
  have htrace : WordTrace (prefixWord ++ tailWord_4660332) baseStart_4660332 baseEnd_4660332 := by
    simpa [prefixWord, tailWord_4660332, baseEnd_4660332] using wordTrace_append hprefix tailTrace_4660332
  have hstable : (prefixWord ++ tailWord_4660332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660332).length < 2 ^ (prefixWord ++ tailWord_4660332).sum := by decide
  have hdescent : baseEnd_4660332 < baseStart_4660332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660349 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_4660349 : Nat := 118140960795 + 4660349 * 2 ^ 59
def prefixEnd_4660349 : Nat := 4983230072969 + 3 ^ 40 * 4660349 * 2
def baseEnd_4660349 : Nat := 797666351566764032268317

theorem tailTrace_4660349 : CollatzResearch.WordTrace tailWord_4660349 prefixEnd_4660349 797666351566764032268317 := by
  unfold tailWord_4660349
  simp only [CollatzResearch.WordTrace]
  refine ⟨169976892193358972087544101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113317928128905981391696067 169976892193358972087544101)
  ·
    refine ⟨31870667286254807266414519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169976892193358972087544101 31870667286254807266414519)
    ·
      refine ⟨47806000929382210899621779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31870667286254807266414519 47806000929382210899621779)
      ·
        refine ⟨71709001394073316349432669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47806000929382210899621779 71709001394073316349432669)
        ·
          refine ⟨26890875522777493631037251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71709001394073316349432669 26890875522777493631037251)
          ·
            refine ⟨40336313284166240446555877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26890875522777493631037251 40336313284166240446555877)
            ·
              refine ⟨7563058740781170083729227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40336313284166240446555877 7563058740781170083729227)
              ·
                refine ⟨11344588111171755125593841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7563058740781170083729227 11344588111171755125593841)
                ·
                  refine ⟨8508441083378816344195381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11344588111171755125593841 8508441083378816344195381)
                  ·
                    refine ⟨797666351566764032268317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8508441083378816344195381 797666351566764032268317)
                    ·
                      rfl

theorem cell23_4660349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_4660349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660349 prefixEnd_4660349 := by exact prefixLift 4660349
  have htrace : WordTrace (prefixWord ++ tailWord_4660349) baseStart_4660349 baseEnd_4660349 := by
    simpa [prefixWord, tailWord_4660349, baseEnd_4660349] using wordTrace_append hprefix tailTrace_4660349
  have hstable : (prefixWord ++ tailWord_4660349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660349).length < 2 ^ (prefixWord ++ tailWord_4660349).sum := by decide
  have hdescent : baseEnd_4660349 < baseStart_4660349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660352 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_4660352 : Nat := 118140960795 + 4660352 * 2 ^ 59
def prefixEnd_4660352 : Nat := 4983230072969 + 3 ^ 40 * 4660352 * 2
def baseEnd_4660352 : Nat := 2393000595142255585067437

theorem tailTrace_4660352 : CollatzResearch.WordTrace tailWord_4660352 prefixEnd_4660352 2393000595142255585067437 := by
  unfold tailWord_4660352
  simp only [CollatzResearch.WordTrace]
  refine ⟨84988500806174051799951655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113318001074898735733268873 84988500806174051799951655)
  ·
    refine ⟨127482751209261077699927483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84988500806174051799951655 127482751209261077699927483)
    ·
      refine ⟨191224126813891616549891225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127482751209261077699927483 191224126813891616549891225)
      ·
        refine ⟨143418095110418712412418419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191224126813891616549891225 143418095110418712412418419)
        ·
          refine ⟨215127142665628068618627629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143418095110418712412418419 215127142665628068618627629)
          ·
            refine ⟨80672678499610525731985361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215127142665628068618627629 80672678499610525731985361)
            ·
              refine ⟨60504508874707894298989021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80672678499610525731985361 60504508874707894298989021)
              ·
                refine ⟨22689190828015460362120883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60504508874707894298989021 22689190828015460362120883)
                ·
                  refine ⟨34033786242023190543181325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22689190828015460362120883 34033786242023190543181325)
                  ·
                    refine ⟨12762669840758696453692997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34033786242023190543181325 12762669840758696453692997)
                    ·
                      refine ⟨2393000595142255585067437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12762669840758696453692997 2393000595142255585067437)
                      ·
                        rfl

theorem cell23_4660352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_4660352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660352 prefixEnd_4660352 := by exact prefixLift 4660352
  have htrace : WordTrace (prefixWord ++ tailWord_4660352) baseStart_4660352 baseEnd_4660352 := by
    simpa [prefixWord, tailWord_4660352, baseEnd_4660352] using wordTrace_append hprefix tailTrace_4660352
  have hstable : (prefixWord ++ tailWord_4660352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660352).length < 2 ^ (prefixWord ++ tailWord_4660352).sum := by decide
  have hdescent : baseEnd_4660352 < baseStart_4660352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660426 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_4660426 : Nat := 118140960795 + 4660426 * 2 ^ 59
def prefixEnd_4660426 : Nat := 4983230072969 + 3 ^ 40 * 4660426 * 2
def baseEnd_4660426 : Nat := 265893176967854255060233

theorem tailTrace_4660426 : CollatzResearch.WordTrace tailWord_4660426 prefixEnd_4660426 265893176967854255060233 := by
  unfold tailWord_4660426
  simp only [CollatzResearch.WordTrace]
  refine ⟨42494925153520003559524283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113319800409386676158731421 42494925153520003559524283)
  ·
    refine ⟨63742387730280005339286425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42494925153520003559524283 63742387730280005339286425)
    ·
      refine ⟨47806790797710004004464819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63742387730280005339286425 47806790797710004004464819)
      ·
        refine ⟨71710186196565006006697229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47806790797710004004464819 71710186196565006006697229)
        ·
          refine ⟨26891319823711877252511461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71710186196565006006697229 26891319823711877252511461)
          ·
            refine ⟨5042122466945976984845899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26891319823711877252511461 5042122466945976984845899)
            ·
              refine ⟨7563183700418965477268849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042122466945976984845899 7563183700418965477268849)
              ·
                refine ⟨5672387775314224107951637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7563183700418965477268849 5672387775314224107951637)
                ·
                  refine ⟨265893176967854255060233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5672387775314224107951637 265893176967854255060233)
                  ·
                    rfl

theorem cell23_4660426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_4660426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660426 prefixEnd_4660426 := by exact prefixLift 4660426
  have htrace : WordTrace (prefixWord ++ tailWord_4660426) baseStart_4660426 baseEnd_4660426 := by
    simpa [prefixWord, tailWord_4660426, baseEnd_4660426] using wordTrace_append hprefix tailTrace_4660426
  have hstable : (prefixWord ++ tailWord_4660426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660426).length < 2 ^ (prefixWord ++ tailWord_4660426).sum := by decide
  have hdescent : baseEnd_4660426 < baseStart_4660426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660456 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 1, 5]
def baseStart_4660456 : Nat := 118140960795 + 4660456 * 2 ^ 59
def prefixEnd_4660456 : Nat := 4983230072969 + 3 ^ 40 * 4660456 * 2
def baseEnd_4660456 : Nat := 797684665710107726055653

theorem tailTrace_4660456 : CollatzResearch.WordTrace tailWord_4660456 prefixEnd_4660456 797684665710107726055653 := by
  unfold tailWord_4660456
  simp only [CollatzResearch.WordTrace]
  refine ⟨84990397401985664680844611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113320529869314219574459481 84990397401985664680844611)
  ·
    refine ⟨127485596102978497021266917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84990397401985664680844611 127485596102978497021266917)
    ·
      refine ⟨23903549269308468191487547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127485596102978497021266917 23903549269308468191487547)
      ·
        refine ⟨35855323903962702287231321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23903549269308468191487547 35855323903962702287231321)
        ·
          refine ⟨26891492927972026715423491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35855323903962702287231321 26891492927972026715423491)
          ·
            refine ⟨40337239391958040073135237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26891492927972026715423491 40337239391958040073135237)
            ·
              refine ⟨7563232385992132513712857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40337239391958040073135237 7563232385992132513712857)
              ·
                refine ⟨5672424289494099385284643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7563232385992132513712857 5672424289494099385284643)
                ·
                  refine ⟨8508636434241149077926965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672424289494099385284643 8508636434241149077926965)
                  ·
                    refine ⟨797684665710107726055653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8508636434241149077926965 797684665710107726055653)
                    ·
                      rfl

theorem cell23_4660456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_4660456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660456 prefixEnd_4660456 := by exact prefixLift 4660456
  have htrace : WordTrace (prefixWord ++ tailWord_4660456) baseStart_4660456 baseEnd_4660456 := by
    simpa [prefixWord, tailWord_4660456, baseEnd_4660456] using wordTrace_append hprefix tailTrace_4660456
  have hstable : (prefixWord ++ tailWord_4660456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660456).length < 2 ^ (prefixWord ++ tailWord_4660456).sum := by decide
  have hdescent : baseEnd_4660456 < baseStart_4660456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660479 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_4660479 : Nat := 118140960795 + 4660479 * 2 ^ 59
def prefixEnd_4660479 : Nat := 4983230072969 + 3 ^ 40 * 4660479 * 2
def baseEnd_4660479 : Nat := 2393065807185376588179353

theorem tailTrace_4660479 : CollatzResearch.WordTrace tailWord_4660479 prefixEnd_4660479 2393065807185376588179353 := by
  unfold tailWord_4660479
  simp only [CollatzResearch.WordTrace]
  refine ⟨169981633682888004289776491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113321089121925336193184327 169981633682888004289776491)
  ·
    refine ⟨254972450524332006434664737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169981633682888004289776491 254972450524332006434664737)
    ·
      refine ⟨191229337893249004825998553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254972450524332006434664737 191229337893249004825998553)
      ·
        refine ⟨143422003419936753619498915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191229337893249004825998553 143422003419936753619498915)
        ·
          refine ⟨215133005129905130429248373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143422003419936753619498915 215133005129905130429248373)
          ·
            refine ⟨20168719230928605977742035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215133005129905130429248373 20168719230928605977742035)
            ·
              refine ⟨30253078846392908966613053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20168719230928605977742035 30253078846392908966613053)
              ·
                refine ⟨11344904567397340862479895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30253078846392908966613053 11344904567397340862479895)
                ·
                  refine ⟨17017356851096011293719843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11344904567397340862479895 17017356851096011293719843)
                  ·
                    refine ⟨25526035276644016940579765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17017356851096011293719843 25526035276644016940579765)
                    ·
                      refine ⟨2393065807185376588179353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25526035276644016940579765 2393065807185376588179353)
                      ·
                        rfl

theorem cell23_4660479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_4660479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660479 prefixEnd_4660479 := by exact prefixLift 4660479
  have htrace : WordTrace (prefixWord ++ tailWord_4660479) baseStart_4660479 baseEnd_4660479 := by
    simpa [prefixWord, tailWord_4660479, baseEnd_4660479] using wordTrace_append hprefix tailTrace_4660479
  have hstable : (prefixWord ++ tailWord_4660479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660479).length < 2 ^ (prefixWord ++ tailWord_4660479).sum := by decide
  have hdescent : baseEnd_4660479 < baseStart_4660479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660510 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4660510 : Nat := 118140960795 + 4660510 * 2 ^ 59
def prefixEnd_4660510 : Nat := 4983230072969 + 3 ^ 40 * 4660510 * 2
def baseEnd_4660510 : Nat := 2393081725085665966891711

theorem tailTrace_4660510 : CollatzResearch.WordTrace tailWord_4660510 prefixEnd_4660510 2393081725085665966891711 := by
  unfold tailWord_4660510
  simp only [CollatzResearch.WordTrace]
  refine ⟨21247845543221962073019373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113321842897183797722769989 21247845543221962073019373)
  ·
    refine ⟨7967942078708235777382265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21247845543221962073019373 7967942078708235777382265)
    ·
      refine ⟨5975956559031176833036699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7967942078708235777382265 5975956559031176833036699)
      ·
        refine ⟨8963934838546765249555049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5975956559031176833036699 8963934838546765249555049)
        ·
          refine ⟨6722951128910073937166287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8963934838546765249555049 6722951128910073937166287)
          ·
            refine ⟨10084426693365110905749431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722951128910073937166287 10084426693365110905749431)
            ·
              refine ⟨15126640040047666358624147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10084426693365110905749431 15126640040047666358624147)
              ·
                refine ⟨22689960060071499537936221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15126640040047666358624147 22689960060071499537936221)
                ·
                  refine ⟨8508735022526812326726083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22689960060071499537936221 8508735022526812326726083)
                  ·
                    refine ⟨12763102533790218490089125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8508735022526812326726083 12763102533790218490089125)
                    ·
                      refine ⟨2393081725085665966891711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12763102533790218490089125 2393081725085665966891711)
                      ·
                        rfl

theorem cell23_4660510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4660510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660510 prefixEnd_4660510 := by exact prefixLift 4660510
  have htrace : WordTrace (prefixWord ++ tailWord_4660510) baseStart_4660510 baseEnd_4660510 := by
    simpa [prefixWord, tailWord_4660510, baseEnd_4660510] using wordTrace_append hprefix tailTrace_4660510
  have hstable : (prefixWord ++ tailWord_4660510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660510).length < 2 ^ (prefixWord ++ tailWord_4660510).sum := by decide
  have hdescent : baseEnd_4660510 < baseStart_4660510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660530 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_4660530 : Nat := 118140960795 + 4660530 * 2 ^ 59
def prefixEnd_4660530 : Nat := 4983230072969 + 3 ^ 40 * 4660530 * 2
def baseEnd_4660530 : Nat := 2393091994698755888641619

theorem tailTrace_4660530 : CollatzResearch.WordTrace tailWord_4660530 prefixEnd_4660530 2393091994698755888641619 := by
  unfold tailWord_4660530
  simp only [CollatzResearch.WordTrace]
  refine ⟨42495873451425809999970761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113322329203802159999922029 42495873451425809999970761)
  ·
    refine ⟨31871905088569357499978071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42495873451425809999970761 31871905088569357499978071)
    ·
      refine ⟨47807857632854036249967107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31871905088569357499978071 47807857632854036249967107)
      ·
        refine ⟨71711786449281054374950661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47807857632854036249967107 71711786449281054374950661)
        ·
          refine ⟨13445959959240197695303249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71711786449281054374950661 13445959959240197695303249)
          ·
            refine ⟨10084469969430148271477437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13445959959240197695303249 10084469969430148271477437)
            ·
              refine ⟨3781676238536305601804039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10084469969430148271477437 3781676238536305601804039)
              ·
                refine ⟨5672514357804458402706059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781676238536305601804039 5672514357804458402706059)
                ·
                  refine ⟨8508771536706687604059089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672514357804458402706059 8508771536706687604059089)
                  ·
                    refine ⟨6381578652530015703044317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8508771536706687604059089 6381578652530015703044317)
                    ·
                      refine ⟨2393091994698755888641619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6381578652530015703044317 2393091994698755888641619)
                      ·
                        rfl

theorem cell23_4660530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_4660530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660530 prefixEnd_4660530 := by exact prefixLift 4660530
  have htrace : WordTrace (prefixWord ++ tailWord_4660530) baseStart_4660530 baseEnd_4660530 := by
    simpa [prefixWord, tailWord_4660530, baseEnd_4660530] using wordTrace_append hprefix tailTrace_4660530
  have hstable : (prefixWord ++ tailWord_4660530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660530).length < 2 ^ (prefixWord ++ tailWord_4660530).sum := by decide
  have hdescent : baseEnd_4660530 < baseStart_4660530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660543 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 3]
def baseStart_4660543 : Nat := 118140960795 + 4660543 * 2 ^ 59
def prefixEnd_4660543 : Nat := 4983230072969 + 3 ^ 40 * 4660543 * 2
def baseEnd_4660543 : Nat := 2393098669947264337779059

theorem tailTrace_4660543 : CollatzResearch.WordTrace tailWord_4660543 prefixEnd_4660543 2393098669947264337779059 := by
  unfold tailWord_4660543
  simp only [CollatzResearch.WordTrace]
  refine ⟨169983967954656143220106283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113322645303104095480070855 169983967954656143220106283)
  ·
    refine ⟨254975951931984214830159425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169983967954656143220106283 254975951931984214830159425)
    ·
      refine ⟨191231963948988161122619569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254975951931984214830159425 191231963948988161122619569)
      ·
        refine ⟨143423972961741120841964677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191231963948988161122619569 143423972961741120841964677)
        ·
          refine ⟨26891994930326460157868377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143423972961741120841964677 26891994930326460157868377)
          ·
            refine ⟨20168996197744845118401283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26891994930326460157868377 20168996197744845118401283)
            ·
              refine ⟨30253494296617267677601925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20168996197744845118401283 30253494296617267677601925)
              ·
                refine ⟨5672530180615737689550361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30253494296617267677601925 5672530180615737689550361)
                ·
                  refine ⟨4254397635461803267162771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5672530180615737689550361 4254397635461803267162771)
                  ·
                    refine ⟨6381596453192704900744157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4254397635461803267162771 6381596453192704900744157)
                    ·
                      refine ⟨2393098669947264337779059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6381596453192704900744157 2393098669947264337779059)
                      ·
                        rfl

theorem cell23_4660543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_4660543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660543 prefixEnd_4660543 := by exact prefixLift 4660543
  have htrace : WordTrace (prefixWord ++ tailWord_4660543) baseStart_4660543 baseEnd_4660543 := by
    simpa [prefixWord, tailWord_4660543, baseEnd_4660543] using wordTrace_append hprefix tailTrace_4660543
  have hstable : (prefixWord ++ tailWord_4660543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660543).length < 2 ^ (prefixWord ++ tailWord_4660543).sum := by decide
  have hdescent : baseEnd_4660543 < baseStart_4660543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660569 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_4660569 : Nat := 118140960795 + 4660569 * 2 ^ 59
def prefixEnd_4660569 : Nat := 4983230072969 + 3 ^ 40 * 4660569 * 2
def baseEnd_4660569 : Nat := 2393112020444281236053939

theorem tailTrace_4660569 : CollatzResearch.WordTrace tailWord_4660569 prefixEnd_4660569 2393112020444281236053939 := by
  unfold tailWord_4660569
  simp only [CollatzResearch.WordTrace]
  refine ⟨169984916252561949660552761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113323277501707966440368507 169984916252561949660552761)
  ·
    refine ⟨127488687189421462245414571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169984916252561949660552761 127488687189421462245414571)
    ·
      refine ⟨191233030784132193368121857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127488687189421462245414571 191233030784132193368121857)
      ·
        refine ⟨143424773088099145026091393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191233030784132193368121857 143424773088099145026091393)
        ·
          refine ⟨107568579816074358769568545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143424773088099145026091393 107568579816074358769568545)
          ·
            refine ⟨80676434862055769077176409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107568579816074358769568545 80676434862055769077176409)
            ·
              refine ⟨60507326146541826807882307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80676434862055769077176409 60507326146541826807882307)
              ·
                refine ⟨90760989219812740211823461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60507326146541826807882307 90760989219812740211823461)
                ·
                  refine ⟨17017685478714888789716899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90760989219812740211823461 17017685478714888789716899)
                  ·
                    refine ⟨25526528218072333184575349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17017685478714888789716899 25526528218072333184575349)
                    ·
                      refine ⟨2393112020444281236053939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25526528218072333184575349 2393112020444281236053939)
                      ·
                        rfl

theorem cell23_4660569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_4660569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660569 prefixEnd_4660569 := by exact prefixLift 4660569
  have htrace : WordTrace (prefixWord ++ tailWord_4660569) baseStart_4660569 baseEnd_4660569 := by
    simpa [prefixWord, tailWord_4660569, baseEnd_4660569] using wordTrace_append hprefix tailTrace_4660569
  have hstable : (prefixWord ++ tailWord_4660569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660569).length < 2 ^ (prefixWord ++ tailWord_4660569).sum := by decide
  have hdescent : baseEnd_4660569 < baseStart_4660569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660617 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 1, 4, 2]
def baseStart_4660617 : Nat := 118140960795 + 4660617 * 2 ^ 59
def prefixEnd_4660617 : Nat := 4983230072969 + 3 ^ 40 * 4660617 * 2
def baseEnd_4660617 : Nat := 2393136667515697048253719

theorem tailTrace_4660617 : CollatzResearch.WordTrace tailWord_4660617 prefixEnd_4660617 2393136667515697048253719 := by
  unfold tailWord_4660617
  simp only [CollatzResearch.WordTrace]
  refine ⟨169986666956388053858300105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113324444637592035905533403 169986666956388053858300105)
  ·
    refine ⟨127490000217291040393725079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169986666956388053858300105 127490000217291040393725079)
    ·
      refine ⟨191235000325936560590587619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127490000217291040393725079 191235000325936560590587619)
      ·
        refine ⟨286852500488904840885881429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191235000325936560590587619 286852500488904840885881429)
        ·
          refine ⟨3361552740104353604131423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 286852500488904840885881429 3361552740104353604131423)
          ·
            refine ⟨5042329110156530406197135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361552740104353604131423 5042329110156530406197135)
            ·
              refine ⟨7563493665234795609295703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042329110156530406197135 7563493665234795609295703)
              ·
                refine ⟨11345240497852193413943555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7563493665234795609295703 11345240497852193413943555)
                ·
                  refine ⟨17017860746778290120915333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11345240497852193413943555 17017860746778290120915333)
                  ·
                    refine ⟨3190848890020929397671625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17017860746778290120915333 3190848890020929397671625)
                    ·
                      refine ⟨2393136667515697048253719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3190848890020929397671625 2393136667515697048253719)
                      ·
                        rfl

theorem cell23_4660617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 4, 2].length) (baseStart_4660617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660617 prefixEnd_4660617 := by exact prefixLift 4660617
  have htrace : WordTrace (prefixWord ++ tailWord_4660617) baseStart_4660617 baseEnd_4660617 := by
    simpa [prefixWord, tailWord_4660617, baseEnd_4660617] using wordTrace_append hprefix tailTrace_4660617
  have hstable : (prefixWord ++ tailWord_4660617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660617).length < 2 ^ (prefixWord ++ tailWord_4660617).sum := by decide
  have hdescent : baseEnd_4660617 < baseStart_4660617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660619 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 3, 7]
def baseStart_4660619 : Nat := 118140960795 + 4660619 * 2 ^ 59
def prefixEnd_4660619 : Nat := 4983230072969 + 3 ^ 40 * 4660619 * 2
def baseEnd_4660619 : Nat := 797712564825668680142903

theorem tailTrace_4660619 : CollatzResearch.WordTrace tailWord_4660619 prefixEnd_4660619 797712564825668680142903 := by
  unfold tailWord_4660619
  simp only [CollatzResearch.WordTrace]
  refine ⟨169986739902380808199872911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113324493268253872133248607 169986739902380808199872911)
  ·
    refine ⟨254980109853571212299809367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169986739902380808199872911 254980109853571212299809367)
    ·
      refine ⟨382470164780356818449714051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254980109853571212299809367 382470164780356818449714051)
      ·
        refine ⟨573705247170535227674571077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382470164780356818449714051 573705247170535227674571077)
        ·
          refine ⟨107569733844475355188982077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 573705247170535227674571077 107569733844475355188982077)
          ·
            refine ⟨40338650191678258195868279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107569733844475355188982077 40338650191678258195868279)
            ·
              refine ⟨60507975287517387293802419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40338650191678258195868279 60507975287517387293802419)
              ·
                refine ⟨90761962931276080940703629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60507975287517387293802419 90761962931276080940703629)
                ·
                  refine ⟨34035736099228530352763861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90761962931276080940703629 34035736099228530352763861)
                  ·
                    refine ⟨797712564825668680142903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34035736099228530352763861 797712564825668680142903)
                    ·
                      rfl

theorem cell23_4660619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_4660619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660619 prefixEnd_4660619 := by exact prefixLift 4660619
  have htrace : WordTrace (prefixWord ++ tailWord_4660619) baseStart_4660619 baseEnd_4660619 := by
    simpa [prefixWord, tailWord_4660619, baseEnd_4660619] using wordTrace_append hprefix tailTrace_4660619
  have hstable : (prefixWord ++ tailWord_4660619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660619).length < 2 ^ (prefixWord ++ tailWord_4660619).sum := by decide
  have hdescent : baseEnd_4660619 < baseStart_4660619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660653 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_4660653 : Nat := 118140960795 + 4660653 * 2 ^ 59
def prefixEnd_4660653 : Nat := 4983230072969 + 3 ^ 40 * 4660653 * 2
def baseEnd_4660653 : Nat := 797718384273086302467851

theorem tailTrace_4660653 : CollatzResearch.WordTrace tailWord_4660653 prefixEnd_4660653 797718384273086302467851 := by
  unfold tailWord_4660653
  simp only [CollatzResearch.WordTrace]
  refine ⟨169987979984257632006610613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113325319989505088004407075 169987979984257632006610613)
  ·
    refine ⟨15936373123524153000619745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169987979984257632006610613 15936373123524153000619745)
    ·
      refine ⟨11952279842643114750464809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15936373123524153000619745 11952279842643114750464809)
      ·
        refine ⟨8964209881982336062848607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11952279842643114750464809 8964209881982336062848607)
        ·
          refine ⟨13446314822973504094272911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8964209881982336062848607 13446314822973504094272911)
          ·
            refine ⟨20169472234460256141409367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13446314822973504094272911 20169472234460256141409367)
            ·
              refine ⟨30254208351690384212114051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20169472234460256141409367 30254208351690384212114051)
              ·
                refine ⟨45381312527535576318171077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30254208351690384212114051 45381312527535576318171077)
                ·
                  refine ⟨8508996098912920559657077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45381312527535576318171077 8508996098912920559657077)
                  ·
                    refine ⟨797718384273086302467851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8508996098912920559657077 797718384273086302467851)
                    ·
                      rfl

theorem cell23_4660653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_4660653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660653 prefixEnd_4660653 := by exact prefixLift 4660653
  have htrace : WordTrace (prefixWord ++ tailWord_4660653) baseStart_4660653 baseEnd_4660653 := by
    simpa [prefixWord, tailWord_4660653, baseEnd_4660653] using wordTrace_append hprefix tailTrace_4660653
  have hstable : (prefixWord ++ tailWord_4660653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660653).length < 2 ^ (prefixWord ++ tailWord_4660653).sum := by decide
  have hdescent : baseEnd_4660653 < baseStart_4660653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660686 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_4660686 : Nat := 118140960795 + 4660686 * 2 ^ 59
def prefixEnd_4660686 : Nat := 4983230072969 + 3 ^ 40 * 4660686 * 2
def baseEnd_4660686 : Nat := 2393172097680857278290901

theorem tailTrace_4660686 : CollatzResearch.WordTrace tailWord_4660686 prefixEnd_4660686 2393172097680857278290901 := by
  unfold tailWord_4660686
  simp only [CollatzResearch.WordTrace]
  refine ⟨21248647949142259830320239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113326122395425385761707941 21248647949142259830320239)
  ·
    refine ⟨31872971923713389745480359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21248647949142259830320239 31872971923713389745480359)
    ·
      refine ⟨47809457885570084618220539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31872971923713389745480359 47809457885570084618220539)
      ·
        refine ⟨71714186828355126927330809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47809457885570084618220539 71714186828355126927330809)
        ·
          refine ⟨53785640121266345195498107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71714186828355126927330809 53785640121266345195498107)
          ·
            refine ⟨80678460181899517793247161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53785640121266345195498107 80678460181899517793247161)
            ·
              refine ⟨60508845136424638344935371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80678460181899517793247161 60508845136424638344935371)
              ·
                refine ⟨90763267704636957517403057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60508845136424638344935371 90763267704636957517403057)
                ·
                  refine ⟨68072450778477718138052293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90763267704636957517403057 68072450778477718138052293)
                  ·
                    refine ⟨12763584520964572150884805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68072450778477718138052293 12763584520964572150884805)
                    ·
                      refine ⟨2393172097680857278290901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12763584520964572150884805 2393172097680857278290901)
                      ·
                        rfl

theorem cell23_4660686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_4660686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660686 prefixEnd_4660686 := by exact prefixLift 4660686
  have htrace : WordTrace (prefixWord ++ tailWord_4660686) baseStart_4660686 baseEnd_4660686 := by
    simpa [prefixWord, tailWord_4660686, baseEnd_4660686] using wordTrace_append hprefix tailTrace_4660686
  have hstable : (prefixWord ++ tailWord_4660686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660686).length < 2 ^ (prefixWord ++ tailWord_4660686).sum := by decide
  have hdescent : baseEnd_4660686 < baseStart_4660686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660743 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 3, 5]
def baseStart_4660743 : Nat := 118140960795 + 4660743 * 2 ^ 59
def prefixEnd_4660743 : Nat := 4983230072969 + 3 ^ 40 * 4660743 * 2
def baseEnd_4660743 : Nat := 797733788692721185092713

theorem tailTrace_4660743 : CollatzResearch.WordTrace tailWord_4660743 prefixEnd_4660743 797733788692721185092713 := by
  unfold tailWord_4660743
  simp only [CollatzResearch.WordTrace]
  refine ⟨169991262553931577377386883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113327508369287718251591255 169991262553931577377386883)
  ·
    refine ⟨254986893830897366066080325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169991262553931577377386883 254986893830897366066080325)
    ·
      refine ⟨47810042593293256137390061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254986893830897366066080325 47810042593293256137390061)
      ·
        refine ⟨17928765972484971051521273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47810042593293256137390061 17928765972484971051521273)
        ·
          refine ⟨13446574479363728288640955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17928765972484971051521273 13446574479363728288640955)
          ·
            refine ⟨20169861719045592432961433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13446574479363728288640955 20169861719045592432961433)
            ·
              refine ⟨15127396289284194324721075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20169861719045592432961433 15127396289284194324721075)
              ·
                refine ⟨22691094433926291487081613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15127396289284194324721075 22691094433926291487081613)
                ·
                  refine ⟨8509160412722359307655605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22691094433926291487081613 8509160412722359307655605)
                  ·
                    refine ⟨797733788692721185092713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8509160412722359307655605 797733788692721185092713)
                    ·
                      rfl

theorem cell23_4660743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_4660743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660743 prefixEnd_4660743 := by exact prefixLift 4660743
  have htrace : WordTrace (prefixWord ++ tailWord_4660743) baseStart_4660743 baseEnd_4660743 := by
    simpa [prefixWord, tailWord_4660743, baseEnd_4660743] using wordTrace_append hprefix tailTrace_4660743
  have hstable : (prefixWord ++ tailWord_4660743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660743).length < 2 ^ (prefixWord ++ tailWord_4660743).sum := by decide
  have hdescent : baseEnd_4660743 < baseStart_4660743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660757 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_4660757 : Nat := 118140960795 + 4660757 * 2 ^ 59
def prefixEnd_4660757 : Nat := 4983230072969 + 3 ^ 40 * 4660757 * 2
def baseEnd_4660757 : Nat := 2393208554807326500503075

theorem tailTrace_4660757 : CollatzResearch.WordTrace tailWord_4660757 prefixEnd_4660757 2393208554807326500503075 := by
  unfold tailWord_4660757
  simp only [CollatzResearch.WordTrace]
  refine ⟨169991773175880857768396525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113327848783920571845597683 169991773175880857768396525)
  ·
    refine ⟨63746914940955321663148697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169991773175880857768396525 63746914940955321663148697)
    ·
      refine ⟨47810186205716491247361523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63746914940955321663148697 47810186205716491247361523)
      ·
        refine ⟨71715279308574736871042285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47810186205716491247361523 71715279308574736871042285)
        ·
          refine ⟨26893229740715526326640857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71715279308574736871042285 26893229740715526326640857)
          ·
            refine ⟨20169922305536644744980643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26893229740715526326640857 20169922305536644744980643)
            ·
              refine ⟨30254883458304967117470965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20169922305536644744980643 30254883458304967117470965)
              ·
                refine ⟨2836395324216090667262903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30254883458304967117470965 2836395324216090667262903)
                ·
                  refine ⟨4254592986324136000894355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836395324216090667262903 4254592986324136000894355)
                  ·
                    refine ⟨6381889479486204001341533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4254592986324136000894355 6381889479486204001341533)
                    ·
                      refine ⟨2393208554807326500503075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6381889479486204001341533 2393208554807326500503075)
                      ·
                        rfl

theorem cell23_4660757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_4660757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660757 prefixEnd_4660757 := by exact prefixLift 4660757
  have htrace : WordTrace (prefixWord ++ tailWord_4660757) baseStart_4660757 baseEnd_4660757 := by
    simpa [prefixWord, tailWord_4660757, baseEnd_4660757] using wordTrace_append hprefix tailTrace_4660757
  have hstable : (prefixWord ++ tailWord_4660757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660757).length < 2 ^ (prefixWord ++ tailWord_4660757).sum := by decide
  have hdescent : baseEnd_4660757 < baseStart_4660757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660760 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 1, 5]
def baseStart_4660760 : Nat := 118140960795 + 4660760 * 2 ^ 59
def prefixEnd_4660760 : Nat := 4983230072969 + 3 ^ 40 * 4660760 * 2
def baseEnd_4660760 : Nat := 797736698416429996255187

theorem tailTrace_4660760 : CollatzResearch.WordTrace tailWord_4660760 prefixEnd_4660760 797736698416429996255187 := by
  unfold tailWord_4660760
  simp only [CollatzResearch.WordTrace]
  refine ⟨84995941297434994640377867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113327921729913326187170489 84995941297434994640377867)
  ·
    refine ⟨127493911946152491960566801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84995941297434994640377867 127493911946152491960566801)
    ·
      refine ⟨95620433959614368970425101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127493911946152491960566801 95620433959614368970425101)
      ·
        refine ⟨35857662734855388363909413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95620433959614368970425101 35857662734855388363909413)
        ·
          refine ⟨6723311762785385318233015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35857662734855388363909413 6723311762785385318233015)
          ·
            refine ⟨10084967644178077977349523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6723311762785385318233015 10084967644178077977349523)
            ·
              refine ⟨15127451466267116966024285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10084967644178077977349523 15127451466267116966024285)
              ·
                refine ⟨5672794299850168862259107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15127451466267116966024285 5672794299850168862259107)
                ·
                  refine ⟨8509191449775253293388661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672794299850168862259107 8509191449775253293388661)
                  ·
                    refine ⟨797736698416429996255187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8509191449775253293388661 797736698416429996255187)
                    ·
                      rfl

theorem cell23_4660760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_4660760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660760 prefixEnd_4660760 := by exact prefixLift 4660760
  have htrace : WordTrace (prefixWord ++ tailWord_4660760) baseStart_4660760 baseEnd_4660760 := by
    simpa [prefixWord, tailWord_4660760, baseEnd_4660760] using wordTrace_append hprefix tailTrace_4660760
  have hstable : (prefixWord ++ tailWord_4660760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660760).length < 2 ^ (prefixWord ++ tailWord_4660760).sum := by decide
  have hdescent : baseEnd_4660760 < baseStart_4660760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660786 : List Nat := [3, 2, 1, 1, 2, 1, 1, 12]
def baseStart_4660786 : Nat := 118140960795 + 4660786 * 2 ^ 59
def prefixEnd_4660786 : Nat := 4983230072969 + 3 ^ 40 * 4660786 * 2
def baseEnd_4660786 : Nat := 88637905398011366186683

theorem tailTrace_4660786 : CollatzResearch.WordTrace tailWord_4660786 prefixEnd_4660786 88637905398011366186683 := by
  unfold tailWord_4660786
  simp only [CollatzResearch.WordTrace]
  refine ⟨42498207723193948930300553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113328553928517197147468141 42498207723193948930300553)
  ·
    refine ⟨31873655792395461697725415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42498207723193948930300553 31873655792395461697725415)
    ·
      refine ⟨47810483688593192546588123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31873655792395461697725415 47810483688593192546588123)
      ·
        refine ⟨71715725532889788819882185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47810483688593192546588123 71715725532889788819882185)
        ·
          refine ⟨53786794149667341614911639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71715725532889788819882185 53786794149667341614911639)
          ·
            refine ⟨80680191224501012422367459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53786794149667341614911639 80680191224501012422367459)
            ·
              refine ⟨121020286836751518633551189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80680191224501012422367459 121020286836751518633551189)
              ·
                refine ⟨88637905398011366186683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 121020286836751518633551189 88637905398011366186683)
                ·
                  rfl

theorem cell23_4660786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_4660786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660786 prefixEnd_4660786 := by exact prefixLift 4660786
  have htrace : WordTrace (prefixWord ++ tailWord_4660786) baseStart_4660786 baseEnd_4660786 := by
    simpa [prefixWord, tailWord_4660786, baseEnd_4660786] using wordTrace_append hprefix tailTrace_4660786
  have hstable : (prefixWord ++ tailWord_4660786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660786).length < 2 ^ (prefixWord ++ tailWord_4660786).sum := by decide
  have hdescent : baseEnd_4660786 < baseStart_4660786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660793 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4660793 : Nat := 118140960795 + 4660793 * 2 ^ 59
def prefixEnd_4660793 : Nat := 4983230072969 + 3 ^ 40 * 4660793 * 2
def baseEnd_4660793 : Nat := 2393227040110888359652909

theorem tailTrace_4660793 : CollatzResearch.WordTrace tailWord_4660793 prefixEnd_4660793 2393227040110888359652909 := by
  unfold tailWord_4660793
  simp only [CollatzResearch.WordTrace]
  refine ⟨169993086203750435916707033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113328724135833623944471355 169993086203750435916707033)
  ·
    refine ⟨127494814652812826937530275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169993086203750435916707033 127494814652812826937530275)
    ·
      refine ⟨191242221979219240406295413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127494814652812826937530275 191242221979219240406295413)
      ·
        refine ⟨17928958310551803788090195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191242221979219240406295413 17928958310551803788090195)
        ·
          refine ⟨26893437465827705682135293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17928958310551803788090195 26893437465827705682135293)
          ·
            refine ⟨10085039049685389630800735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26893437465827705682135293 10085039049685389630800735)
            ·
              refine ⟨15127558574528084446201103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10085039049685389630800735 15127558574528084446201103)
              ·
                refine ⟨22691337861792126669301655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15127558574528084446201103 22691337861792126669301655)
                ·
                  refine ⟨34037006792688190003952483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22691337861792126669301655 34037006792688190003952483)
                  ·
                    refine ⟨51055510189032285005928725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34037006792688190003952483 51055510189032285005928725)
                    ·
                      refine ⟨2393227040110888359652909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51055510189032285005928725 2393227040110888359652909)
                      ·
                        rfl

theorem cell23_4660793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4660793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660793 prefixEnd_4660793 := by exact prefixLift 4660793
  have htrace : WordTrace (prefixWord ++ tailWord_4660793) baseStart_4660793 baseEnd_4660793 := by
    simpa [prefixWord, tailWord_4660793, baseEnd_4660793] using wordTrace_append hprefix tailTrace_4660793
  have hstable : (prefixWord ++ tailWord_4660793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660793).length < 2 ^ (prefixWord ++ tailWord_4660793).sum := by decide
  have hdescent : baseEnd_4660793 < baseStart_4660793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660797 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4660797 : Nat := 118140960795 + 4660797 * 2 ^ 59
def prefixEnd_4660797 : Nat := 4983230072969 + 3 ^ 40 * 4660797 * 2
def baseEnd_4660797 : Nat := 2393229094033506344002891

theorem tailTrace_4660797 : CollatzResearch.WordTrace tailWord_4660797 prefixEnd_4660797 2393229094033506344002891 := by
  unfold tailWord_4660797
  simp only [CollatzResearch.WordTrace]
  refine ⟨169993232095735944599852645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113328821397157296399901763 169993232095735944599852645)
  ·
    refine ⟨31873731017950489612472371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169993232095735944599852645 31873731017950489612472371)
    ·
      refine ⟨47810596526925734418708557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31873731017950489612472371 47810596526925734418708557)
      ·
        refine ⟨17928973697597150407015709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47810596526925734418708557 17928973697597150407015709)
        ·
          refine ⟨6723365136598931402630891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17928973697597150407015709 6723365136598931402630891)
          ·
            refine ⟨10085047704898397103946337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6723365136598931402630891 10085047704898397103946337)
            ·
              refine ⟨7563785778673797827959753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10085047704898397103946337 7563785778673797827959753)
              ·
                refine ⟨5672839334005348370969815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7563785778673797827959753 5672839334005348370969815)
                ·
                  refine ⟨8509259001008022556454723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672839334005348370969815 8509259001008022556454723)
                  ·
                    refine ⟨12763888501512033834682085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8509259001008022556454723 12763888501512033834682085)
                    ·
                      refine ⟨2393229094033506344002891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12763888501512033834682085 2393229094033506344002891)
                      ·
                        rfl

theorem cell23_4660797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4660797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660797 prefixEnd_4660797 := by exact prefixLift 4660797
  have htrace : WordTrace (prefixWord ++ tailWord_4660797) baseStart_4660797 baseEnd_4660797 := by
    simpa [prefixWord, tailWord_4660797, baseEnd_4660797] using wordTrace_append hprefix tailTrace_4660797
  have hstable : (prefixWord ++ tailWord_4660797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660797).length < 2 ^ (prefixWord ++ tailWord_4660797).sum := by decide
  have hdescent : baseEnd_4660797 < baseStart_4660797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660873 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_4660873 : Nat := 118140960795 + 4660873 * 2 ^ 59
def prefixEnd_4660873 : Nat := 4983230072969 + 3 ^ 40 * 4660873 * 2
def baseEnd_4660873 : Nat := 2393268118563248046652541

theorem tailTrace_4660873 : CollatzResearch.WordTrace tailWord_4660873 prefixEnd_4660873 2393268118563248046652541 := by
  unfold tailWord_4660873
  simp only [CollatzResearch.WordTrace]
  refine ⟨169996004043460609579619273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113330669362307073053079515 169996004043460609579619273)
  ·
    refine ⟨127497003032595457184714455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169996004043460609579619273 127497003032595457184714455)
    ·
      refine ⟨191245504548893185777071683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127497003032595457184714455 191245504548893185777071683)
      ·
        refine ⟨286868256823339778665607525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191245504548893185777071683 286868256823339778665607525)
        ·
          refine ⟨53787798154376208499801411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286868256823339778665607525 53787798154376208499801411)
          ·
            refine ⟨80681697231564312749702117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53787798154376208499801411 80681697231564312749702117)
            ·
              refine ⟨15127818230918308640569147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80681697231564312749702117 15127818230918308640569147)
              ·
                refine ⟨22691727346377462960853721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15127818230918308640569147 22691727346377462960853721)
                ·
                  refine ⟨17018795509783097220640291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22691727346377462960853721 17018795509783097220640291)
                  ·
                    refine ⟨25528193264674645830960437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17018795509783097220640291 25528193264674645830960437)
                    ·
                      refine ⟨2393268118563248046652541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25528193264674645830960437 2393268118563248046652541)
                      ·
                        rfl

theorem cell23_4660873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_4660873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660873 prefixEnd_4660873 := by exact prefixLift 4660873
  have htrace : WordTrace (prefixWord ++ tailWord_4660873) baseStart_4660873 baseEnd_4660873 := by
    simpa [prefixWord, tailWord_4660873, baseEnd_4660873] using wordTrace_append hprefix tailTrace_4660873
  have hstable : (prefixWord ++ tailWord_4660873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660873).length < 2 ^ (prefixWord ++ tailWord_4660873).sum := by decide
  have hdescent : baseEnd_4660873 < baseStart_4660873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660893 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 7]
def baseStart_4660893 : Nat := 118140960795 + 4660893 * 2 ^ 59
def prefixEnd_4660893 : Nat := 4983230072969 + 3 ^ 40 * 4660893 * 2
def baseEnd_4660893 : Nat := 265919820908481996489161

theorem tailTrace_4660893 : CollatzResearch.WordTrace tailWord_4660893 prefixEnd_4660893 265919820908481996489161 := by
  unfold tailWord_4660893
  simp only [CollatzResearch.WordTrace]
  refine ⟨169996733503388152995347333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113331155668925435330231555 169996733503388152995347333)
  ·
    refine ⟨31874387531885278686627625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169996733503388152995347333 31874387531885278686627625)
    ·
      refine ⟨23905790648913959014970719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31874387531885278686627625 23905790648913959014970719)
      ·
        refine ⟨35858685973370938522456079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23905790648913959014970719 35858685973370938522456079)
        ·
          refine ⟨53788028960056407783684119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35858685973370938522456079 53788028960056407783684119)
          ·
            refine ⟨80682043440084611675526179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53788028960056407783684119 80682043440084611675526179)
            ·
              refine ⟨121023065160126917513289269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80682043440084611675526179 121023065160126917513289269)
              ·
                refine ⟨11345912358761898516870869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121023065160126917513289269 11345912358761898516870869)
                ·
                  refine ⟨265919820908481996489161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11345912358761898516870869 265919820908481996489161)
                  ·
                    rfl

theorem cell23_4660893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_4660893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660893 prefixEnd_4660893 := by exact prefixLift 4660893
  have htrace : WordTrace (prefixWord ++ tailWord_4660893) baseStart_4660893 baseEnd_4660893 := by
    simpa [prefixWord, tailWord_4660893, baseEnd_4660893] using wordTrace_append hprefix tailTrace_4660893
  have hstable : (prefixWord ++ tailWord_4660893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660893).length < 2 ^ (prefixWord ++ tailWord_4660893).sum := by decide
  have hdescent : baseEnd_4660893 < baseStart_4660893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660900 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_4660900 : Nat := 118140960795 + 4660900 * 2 ^ 59
def prefixEnd_4660900 : Nat := 4983230072969 + 3 ^ 40 * 4660900 * 2
def baseEnd_4660900 : Nat := 2393281982540919441014917

theorem tailTrace_4660900 : CollatzResearch.WordTrace tailWord_4660900 prefixEnd_4660900 2393281982540919441014917 := by
  unfold tailWord_4660900
  simp only [CollatzResearch.WordTrace]
  refine ⟨84998494407181396595426077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113331325876241862127234769 84998494407181396595426077)
  ·
    refine ⟨31874435402693023723284779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84998494407181396595426077 31874435402693023723284779)
    ·
      refine ⟨47811653104039535584927169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31874435402693023723284779 47811653104039535584927169)
      ·
        refine ⟨35858739828029651688695377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47811653104039535584927169 35858739828029651688695377)
        ·
          refine ⟨26894054871022238766521533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35858739828029651688695377 26894054871022238766521533)
          ·
            refine ⟨10085270576633339537445575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26894054871022238766521533 10085270576633339537445575)
            ·
              refine ⟨15127905864950009306168363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10085270576633339537445575 15127905864950009306168363)
              ·
                refine ⟨22691858797425013959252545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15127905864950009306168363 22691858797425013959252545)
                ·
                  refine ⟨17018894098068760469439409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22691858797425013959252545 17018894098068760469439409)
                  ·
                    refine ⟨12764170573551570352079557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17018894098068760469439409 12764170573551570352079557)
                    ·
                      refine ⟨2393281982540919441014917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12764170573551570352079557 2393281982540919441014917)
                      ·
                        rfl

theorem cell23_4660900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_4660900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660900 prefixEnd_4660900 := by exact prefixLift 4660900
  have htrace : WordTrace (prefixWord ++ tailWord_4660900) baseStart_4660900 baseEnd_4660900 := by
    simpa [prefixWord, tailWord_4660900, baseEnd_4660900] using wordTrace_append hprefix tailTrace_4660900
  have hstable : (prefixWord ++ tailWord_4660900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660900).length < 2 ^ (prefixWord ++ tailWord_4660900).sum := by decide
  have hdescent : baseEnd_4660900 < baseStart_4660900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660934 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4660934 : Nat := 118140960795 + 4660934 * 2 ^ 59
def prefixEnd_4660934 : Nat := 4983230072969 + 3 ^ 40 * 4660934 * 2
def baseEnd_4660934 : Nat := 2393299440883172307989761

theorem tailTrace_4660934 : CollatzResearch.WordTrace tailWord_4660934 prefixEnd_4660934 2393299440883172307989761 := by
  unfold tailWord_4660934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5312444653007488031174683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113332152597493077998393237 5312444653007488031174683)
  ·
    refine ⟨7968666979511232046762025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5312444653007488031174683 7968666979511232046762025)
    ·
      refine ⟨5976500234633424035071519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7968666979511232046762025 5976500234633424035071519)
      ·
        refine ⟨8964750351950136052607279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5976500234633424035071519 8964750351950136052607279)
        ·
          refine ⟨13447125527925204078910919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8964750351950136052607279 13447125527925204078910919)
          ·
            refine ⟨20170688291887806118366379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13447125527925204078910919 20170688291887806118366379)
            ·
              refine ⟨30256032437831709177549569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20170688291887806118366379 30256032437831709177549569)
              ·
                refine ⟨22692024328373781883162177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30256032437831709177549569 22692024328373781883162177)
                ·
                  refine ⟨17019018246280336412371633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22692024328373781883162177 17019018246280336412371633)
                  ·
                    refine ⟨12764263684710252309278725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17019018246280336412371633 12764263684710252309278725)
                    ·
                      refine ⟨2393299440883172307989761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12764263684710252309278725 2393299440883172307989761)
                      ·
                        rfl

theorem cell23_4660934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4660934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660934 prefixEnd_4660934 := by exact prefixLift 4660934
  have htrace : WordTrace (prefixWord ++ tailWord_4660934) baseStart_4660934 baseEnd_4660934 := by
    simpa [prefixWord, tailWord_4660934, baseEnd_4660934] using wordTrace_append hprefix tailTrace_4660934
  have hstable : (prefixWord ++ tailWord_4660934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660934).length < 2 ^ (prefixWord ++ tailWord_4660934).sum := by decide
  have hdescent : baseEnd_4660934 < baseStart_4660934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660938 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_4660938 : Nat := 118140960795 + 4660938 * 2 ^ 59
def prefixEnd_4660938 : Nat := 4983230072969 + 3 ^ 40 * 4660938 * 2
def baseEnd_4660938 : Nat := 2393301494805790292339743

theorem tailTrace_4660938 : CollatzResearch.WordTrace tailWord_4660938 prefixEnd_4660938 2393301494805790292339743 := by
  unfold tailWord_4660938
  simp only [CollatzResearch.WordTrace]
  refine ⟨42499593697056281420183867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113332249858816750453823645 42499593697056281420183867)
  ·
    refine ⟨63749390545584422130275801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42499593697056281420183867 63749390545584422130275801)
    ·
      refine ⟨47812042909188316597706851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63749390545584422130275801 47812042909188316597706851)
      ·
        refine ⟨71718064363782474896560277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47812042909188316597706851 71718064363782474896560277)
        ·
          refine ⟨3361784267052303510776263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71718064363782474896560277 3361784267052303510776263)
          ·
            refine ⟨5042676400578455266164395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361784267052303510776263 5042676400578455266164395)
            ·
              refine ⟨7564014600867682899246593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042676400578455266164395 7564014600867682899246593)
              ·
                refine ⟨5673010950650762174434945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7564014600867682899246593 5673010950650762174434945)
                ·
                  refine ⟨4254758212988071630826209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5673010950650762174434945 4254758212988071630826209)
                  ·
                    refine ⟨3191068659741053723119657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4254758212988071630826209 3191068659741053723119657)
                    ·
                      refine ⟨2393301494805790292339743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191068659741053723119657 2393301494805790292339743)
                      ·
                        rfl

theorem cell23_4660938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_4660938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660938 prefixEnd_4660938 := by exact prefixLift 4660938
  have htrace : WordTrace (prefixWord ++ tailWord_4660938) baseStart_4660938 baseEnd_4660938 := by
    simpa [prefixWord, tailWord_4660938, baseEnd_4660938] using wordTrace_append hprefix tailTrace_4660938
  have hstable : (prefixWord ++ tailWord_4660938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660938).length < 2 ^ (prefixWord ++ tailWord_4660938).sum := by decide
  have hdescent : baseEnd_4660938 < baseStart_4660938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660983 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 8]
def baseStart_4660983 : Nat := 118140960795 + 4660983 * 2 ^ 59
def prefixEnd_4660983 : Nat := 4983230072969 + 3 ^ 40 * 4660983 * 2
def baseEnd_4660983 : Nat := 265924955715026957364115

theorem tailTrace_4660983 : CollatzResearch.WordTrace tailWord_4660983 prefixEnd_4660983 265924955715026957364115 := by
  unfold tailWord_4660983
  simp only [CollatzResearch.WordTrace]
  refine ⟨170000016073062098366123603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113333344048708065577415735 170000016073062098366123603)
  ·
    refine ⟨255000024109593147549185405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170000016073062098366123603 255000024109593147549185405)
    ·
      refine ⟨95625009041097430330944527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255000024109593147549185405 95625009041097430330944527)
      ·
        refine ⟨143437513561646145496416791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95625009041097430330944527 143437513561646145496416791)
        ·
          refine ⟨215156270342469218244625187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143437513561646145496416791 215156270342469218244625187)
          ·
            refine ⟨322734405513703827366937781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215156270342469218244625187 322734405513703827366937781)
            ·
              refine ⟨30256350516909733815650417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322734405513703827366937781 30256350516909733815650417)
              ·
                refine ⟨22692262887682300361737813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30256350516909733815650417 22692262887682300361737813)
                ·
                  refine ⟨265924955715026957364115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22692262887682300361737813 265924955715026957364115)
                  ·
                    rfl

theorem cell23_4660983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 8].length) (baseStart_4660983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660983 prefixEnd_4660983 := by exact prefixLift 4660983
  have htrace : WordTrace (prefixWord ++ tailWord_4660983) baseStart_4660983 baseEnd_4660983 := by
    simpa [prefixWord, tailWord_4660983, baseEnd_4660983] using wordTrace_append hprefix tailTrace_4660983
  have hstable : (prefixWord ++ tailWord_4660983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660983).length < 2 ^ (prefixWord ++ tailWord_4660983).sum := by decide
  have hdescent : baseEnd_4660983 < baseStart_4660983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4660987 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 1, 4]
def baseStart_4660987 : Nat := 118140960795 + 4660987 * 2 ^ 59
def prefixEnd_4660987 : Nat := 4983230072969 + 3 ^ 40 * 4660987 * 2
def baseEnd_4660987 : Nat := 797775551785953533542339

theorem tailTrace_4660987 : CollatzResearch.WordTrace tailWord_4660987 prefixEnd_4660987 797775551785953533542339 := by
  unfold tailWord_4660987
  simp only [CollatzResearch.WordTrace]
  refine ⟨170000161965047607049269215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113333441310031738032846143 170000161965047607049269215)
  ·
    refine ⟨255000242947571410573903823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170000161965047607049269215 255000242947571410573903823)
    ·
      refine ⟨382500364421357115860855735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255000242947571410573903823 382500364421357115860855735)
      ·
        refine ⟨573750546632035673791283603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382500364421357115860855735 573750546632035673791283603)
        ·
          refine ⟨860625819948053510686925405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573750546632035673791283603 860625819948053510686925405)
          ·
            refine ⟨322734682480520066507597027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 860625819948053510686925405 322734682480520066507597027)
            ·
              refine ⟨484102023720780099761395541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322734682480520066507597027 484102023720780099761395541)
              ·
                refine ⟨2836535295238945897039427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 484102023720780099761395541 2836535295238945897039427)
                ·
                  refine ⟨4254802942858418845559141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836535295238945897039427 4254802942858418845559141)
                  ·
                    refine ⟨797775551785953533542339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4254802942858418845559141 797775551785953533542339)
                    ·
                      rfl

theorem cell23_4660987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 4].length) (baseStart_4660987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4660987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4660987 prefixEnd_4660987 := by exact prefixLift 4660987
  have htrace : WordTrace (prefixWord ++ tailWord_4660987) baseStart_4660987 baseEnd_4660987 := by
    simpa [prefixWord, tailWord_4660987, baseEnd_4660987] using wordTrace_append hprefix tailTrace_4660987
  have hstable : (prefixWord ++ tailWord_4660987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4660987).length < 2 ^ (prefixWord ++ tailWord_4660987).sum := by decide
  have hdescent : baseEnd_4660987 < baseStart_4660987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4660987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661000 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 6]
def baseStart_4661000 : Nat := 118140960795 + 4661000 * 2 ^ 59
def prefixEnd_4661000 : Nat := 4983230072969 + 3 ^ 40 * 4661000 * 2
def baseEnd_4661000 : Nat := 265925925622929894418273

theorem tailTrace_4661000 : CollatzResearch.WordTrace tailWord_4661000 prefixEnd_4661000 265925925622929894418273 := by
  unfold tailWord_4661000
  simp only [CollatzResearch.WordTrace]
  refine ⟨85000318057000255134746227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113333757409333673512994969 85000318057000255134746227)
  ·
    refine ⟨127500477085500382702119341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85000318057000255134746227 127500477085500382702119341)
    ·
      refine ⟨47812678907062643513294753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127500477085500382702119341 47812678907062643513294753)
      ·
        refine ⟨35859509180296982634971065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47812678907062643513294753 35859509180296982634971065)
        ·
          refine ⟨26894631885222736976228299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35859509180296982634971065 26894631885222736976228299)
          ·
            refine ⟨40341947827834105464342449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26894631885222736976228299 40341947827834105464342449)
            ·
              refine ⟨30256460870875579098256837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40341947827834105464342449 30256460870875579098256837)
              ·
                refine ⟨5673086413289171080923157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30256460870875579098256837 5673086413289171080923157)
                ·
                  refine ⟨265925925622929894418273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5673086413289171080923157 265925925622929894418273)
                  ·
                    rfl

theorem cell23_4661000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 6].length) (baseStart_4661000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661000 prefixEnd_4661000 := by exact prefixLift 4661000
  have htrace : WordTrace (prefixWord ++ tailWord_4661000) baseStart_4661000 baseEnd_4661000 := by
    simpa [prefixWord, tailWord_4661000, baseEnd_4661000] using wordTrace_append hprefix tailTrace_4661000
  have hstable : (prefixWord ++ tailWord_4661000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661000).length < 2 ^ (prefixWord ++ tailWord_4661000).sum := by decide
  have hdescent : baseEnd_4661000 < baseStart_4661000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661003 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_4661003 : Nat := 118140960795 + 4661003 * 2 ^ 59
def prefixEnd_4661003 : Nat := 4983230072969 + 3 ^ 40 * 4661003 * 2
def baseEnd_4661003 : Nat := 2393334871048332538026943

theorem tailTrace_4661003 : CollatzResearch.WordTrace tailWord_4661003 prefixEnd_4661003 2393334871048332538026943 := by
  unfold tailWord_4661003
  simp only [CollatzResearch.WordTrace]
  refine ⟨170000745532989641781851663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113333830355326427854567775 170000745532989641781851663)
  ·
    refine ⟨255001118299484462672777495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170000745532989641781851663 255001118299484462672777495)
    ·
      refine ⟨382501677449226694009166243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255001118299484462672777495 382501677449226694009166243)
      ·
        refine ⟨573752516173840041013749365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382501677449226694009166243 573752516173840041013749365)
        ·
          refine ⟨53789298391297503845039003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 573752516173840041013749365 53789298391297503845039003)
          ·
            refine ⟨80683947586946255767558505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53789298391297503845039003 80683947586946255767558505)
            ·
              refine ⟨60512960690209691825668879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80683947586946255767558505 60512960690209691825668879)
              ·
                refine ⟨90769441035314537738503319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60512960690209691825668879 90769441035314537738503319)
                ·
                  refine ⟨136154161552971806607754979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90769441035314537738503319 136154161552971806607754979)
                  ·
                    refine ⟨204231242329457709911632469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136154161552971806607754979 204231242329457709911632469)
                    ·
                      refine ⟨2393334871048332538026943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 204231242329457709911632469 2393334871048332538026943)
                      ·
                        rfl

theorem cell23_4661003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_4661003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661003 prefixEnd_4661003 := by exact prefixLift 4661003
  have htrace : WordTrace (prefixWord ++ tailWord_4661003) baseStart_4661003 baseEnd_4661003 := by
    simpa [prefixWord, tailWord_4661003, baseEnd_4661003] using wordTrace_append hprefix tailTrace_4661003
  have hstable : (prefixWord ++ tailWord_4661003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661003).length < 2 ^ (prefixWord ++ tailWord_4661003).sum := by decide
  have hdescent : baseEnd_4661003 < baseStart_4661003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661027 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 3]
def baseStart_4661027 : Nat := 118140960795 + 4661027 * 2 ^ 59
def prefixEnd_4661027 : Nat := 4983230072969 + 3 ^ 40 * 4661027 * 2
def baseEnd_4661027 : Nat := 2393347194584040444126833

theorem tailTrace_4661027 : CollatzResearch.WordTrace tailWord_4661027 prefixEnd_4661027 2393347194584040444126833 := by
  unfold tailWord_4661027
  simp only [CollatzResearch.WordTrace]
  refine ⟨170001620884902693880725335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113334413923268462587150223 170001620884902693880725335)
  ·
    refine ⟨255002431327354040821088003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170001620884902693880725335 255002431327354040821088003)
    ·
      refine ⟨382503646991031061231632005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255002431327354040821088003 382503646991031061231632005)
      ·
        refine ⟨71719433810818323980931001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382503646991031061231632005 71719433810818323980931001)
        ·
          refine ⟨53789575358113742985698251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71719433810818323980931001 53789575358113742985698251)
          ·
            refine ⟨80684363037170614478547377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53789575358113742985698251 80684363037170614478547377)
            ·
              refine ⟨60513272277877960858910533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80684363037170614478547377 60513272277877960858910533)
              ·
                refine ⟨11346238552102117661045725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60513272277877960858910533 11346238552102117661045725)
                ·
                  refine ⟨4254839457038294122892147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11346238552102117661045725 4254839457038294122892147)
                  ·
                    refine ⟨6382259185557441184338221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4254839457038294122892147 6382259185557441184338221)
                    ·
                      refine ⟨2393347194584040444126833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6382259185557441184338221 2393347194584040444126833)
                      ·
                        rfl

theorem cell23_4661027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_4661027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661027 prefixEnd_4661027 := by exact prefixLift 4661027
  have htrace : WordTrace (prefixWord ++ tailWord_4661027) baseStart_4661027 baseEnd_4661027 := by
    simpa [prefixWord, tailWord_4661027, baseEnd_4661027] using wordTrace_append hprefix tailTrace_4661027
  have hstable : (prefixWord ++ tailWord_4661027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661027).length < 2 ^ (prefixWord ++ tailWord_4661027).sum := by decide
  have hdescent : baseEnd_4661027 < baseStart_4661027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661077 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_4661077 : Nat := 118140960795 + 4661077 * 2 ^ 59
def prefixEnd_4661077 : Nat := 4983230072969 + 3 ^ 40 * 4661077 * 2
def baseEnd_4661077 : Nat := 797790956205588416167201

theorem tailTrace_4661077 : CollatzResearch.WordTrace tailWord_4661077 prefixEnd_4661077 797790956205588416167201 := by
  unfold tailWord_4661077
  simp only [CollatzResearch.WordTrace]
  refine ⟨170003444534721552420045485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113335629689814368280030323 170003444534721552420045485)
  ·
    refine ⟨63751291700520582157517057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170003444534721552420045485 63751291700520582157517057)
    ·
      refine ⟨47813468775390436618137793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63751291700520582157517057 47813468775390436618137793)
      ·
        refine ⟨35860101581542827463603345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47813468775390436618137793 35860101581542827463603345)
        ·
          refine ⟨26895076186157120597702509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35860101581542827463603345 26895076186157120597702509)
          ·
            refine ⟨10085653569808920224138441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26895076186157120597702509 10085653569808920224138441)
            ·
              refine ⟨7564240177356690168103831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10085653569808920224138441 7564240177356690168103831)
              ·
                refine ⟨11346360266035035252155747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7564240177356690168103831 11346360266035035252155747)
                ·
                  refine ⟨17019540399052552878233621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11346360266035035252155747 17019540399052552878233621)
                  ·
                    refine ⟨797790956205588416167201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17019540399052552878233621 797790956205588416167201)
                    ·
                      rfl

theorem cell23_4661077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_4661077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661077 prefixEnd_4661077 := by exact prefixLift 4661077
  have htrace : WordTrace (prefixWord ++ tailWord_4661077) baseStart_4661077 baseEnd_4661077 := by
    simpa [prefixWord, tailWord_4661077, baseEnd_4661077] using wordTrace_append hprefix tailTrace_4661077
  have hstable : (prefixWord ++ tailWord_4661077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661077).length < 2 ^ (prefixWord ++ tailWord_4661077).sum := by decide
  have hdescent : baseEnd_4661077 < baseStart_4661077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661087 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_4661087 : Nat := 118140960795 + 4661087 * 2 ^ 59
def prefixEnd_4661087 : Nat := 4983230072969 + 3 ^ 40 * 4661087 * 2
def baseEnd_4661087 : Nat := 2393378003423310209376557

theorem tailTrace_4661087 : CollatzResearch.WordTrace tailWord_4661087 prefixEnd_4661087 2393378003423310209376557 := by
  unfold tailWord_4661087
  simp only [CollatzResearch.WordTrace]
  refine ⟨170003809264685324127909515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113335872843123549418606343 170003809264685324127909515)
  ·
    refine ⟨255005713897027986191864273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170003809264685324127909515 255005713897027986191864273)
    ·
      refine ⟨191254285422770989643898205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255005713897027986191864273 191254285422770989643898205)
      ·
        refine ⟨71720357033539121116461827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191254285422770989643898205 71720357033539121116461827)
        ·
          refine ⟨107580535550308681674692741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71720357033539121116461827 107580535550308681674692741)
          ·
            refine ⟨20171350415682877814004889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107580535550308681674692741 20171350415682877814004889)
            ·
              refine ⟨15128512811762158360503667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20171350415682877814004889 15128512811762158360503667)
              ·
                refine ⟨22692769217643237540755501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15128512811762158360503667 22692769217643237540755501)
                ·
                  refine ⟨8509788456616214077783313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22692769217643237540755501 8509788456616214077783313)
                  ·
                    refine ⟨6382341342462160558337485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8509788456616214077783313 6382341342462160558337485)
                    ·
                      refine ⟨2393378003423310209376557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6382341342462160558337485 2393378003423310209376557)
                      ·
                        rfl

theorem cell23_4661087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_4661087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661087 prefixEnd_4661087 := by exact prefixLift 4661087
  have htrace : WordTrace (prefixWord ++ tailWord_4661087) baseStart_4661087 baseEnd_4661087 := by
    simpa [prefixWord, tailWord_4661087, baseEnd_4661087] using wordTrace_append hprefix tailTrace_4661087
  have hstable : (prefixWord ++ tailWord_4661087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661087).length < 2 ^ (prefixWord ++ tailWord_4661087).sum := by decide
  have hdescent : baseEnd_4661087 < baseStart_4661087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661098 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_4661098 : Nat := 118140960795 + 4661098 * 2 ^ 59
def prefixEnd_4661098 : Nat := 4983230072969 + 3 ^ 40 * 4661098 * 2
def baseEnd_4661098 : Nat := 797794550570169888779669

theorem tailTrace_4661098 : CollatzResearch.WordTrace tailWord_4661098 prefixEnd_4661098 797794550570169888779669 := by
  unfold tailWord_4661098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42501052616911368251639987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113336140311763648671039965 42501052616911368251639987)
  ·
    refine ⟨63751578925367052377459981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42501052616911368251639987 63751578925367052377459981)
    ·
      refine ⟨23906842097012644641547493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63751578925367052377459981 23906842097012644641547493)
      ·
        refine ⟨4482532893189870870290155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23906842097012644641547493 4482532893189870870290155)
        ·
          refine ⟨6723799339784806305435233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4482532893189870870290155 6723799339784806305435233)
          ·
            refine ⟨5042849504838604729076425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6723799339784806305435233 5042849504838604729076425)
            ·
              refine ⟨3782137128628953546807319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5042849504838604729076425 3782137128628953546807319)
              ·
                refine ⟨5673205692943430320210979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3782137128628953546807319 5673205692943430320210979)
                ·
                  refine ⟨8509808539415145480316469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5673205692943430320210979 8509808539415145480316469)
                  ·
                    refine ⟨797794550570169888779669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8509808539415145480316469 797794550570169888779669)
                    ·
                      rfl

theorem cell23_4661098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_4661098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661098 prefixEnd_4661098 := by exact prefixLift 4661098
  have htrace : WordTrace (prefixWord ++ tailWord_4661098) baseStart_4661098 baseEnd_4661098 := by
    simpa [prefixWord, tailWord_4661098, baseEnd_4661098] using wordTrace_append hprefix tailTrace_4661098
  have hstable : (prefixWord ++ tailWord_4661098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661098).length < 2 ^ (prefixWord ++ tailWord_4661098).sum := by decide
  have hdescent : baseEnd_4661098 < baseStart_4661098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661118 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4661118 : Nat := 118140960795 + 4661118 * 2 ^ 59
def prefixEnd_4661118 : Nat := 4983230072969 + 3 ^ 40 * 4661118 * 2
def baseEnd_4661118 : Nat := 2393393921323599588088915

theorem tailTrace_4661118 : CollatzResearch.WordTrace tailWord_4661118 prefixEnd_4661118 2393393921323599588088915 := by
  unfold tailWord_4661118
  simp only [CollatzResearch.WordTrace]
  refine ⟨21250617490946627052786001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113336626618382010948192005 21250617490946627052786001)
  ·
    refine ⟨15937963118209970289589501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21250617490946627052786001 15937963118209970289589501)
    ·
      refine ⟨5976736169328738858596063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15937963118209970289589501 5976736169328738858596063)
      ·
        refine ⟨8965104253993108287894095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5976736169328738858596063 8965104253993108287894095)
        ·
          refine ⟨13447656380989662431841143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8965104253993108287894095 13447656380989662431841143)
          ·
            refine ⟨20171484571484493647761715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13447656380989662431841143 20171484571484493647761715)
            ·
              refine ⟨30257226857226740471642573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20171484571484493647761715 30257226857226740471642573)
              ·
                refine ⟨11346460071460027676865965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30257226857226740471642573 11346460071460027676865965)
                ·
                  refine ⟨4254922526797510378824737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11346460071460027676865965 4254922526797510378824737)
                  ·
                    refine ⟨3191191895098132784118553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4254922526797510378824737 3191191895098132784118553)
                    ·
                      refine ⟨2393393921323599588088915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191191895098132784118553 2393393921323599588088915)
                      ·
                        rfl

theorem cell23_4661118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4661118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661118 prefixEnd_4661118 := by exact prefixLift 4661118
  have htrace : WordTrace (prefixWord ++ tailWord_4661118) baseStart_4661118 baseEnd_4661118 := by
    simpa [prefixWord, tailWord_4661118, baseEnd_4661118] using wordTrace_append hprefix tailTrace_4661118
  have hstable : (prefixWord ++ tailWord_4661118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661118).length < 2 ^ (prefixWord ++ tailWord_4661118).sum := by decide
  have hdescent : baseEnd_4661118 < baseStart_4661118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661177 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4661177 : Nat := 118140960795 + 4661177 * 2 ^ 59
def prefixEnd_4661177 : Nat := 4983230072969 + 3 ^ 40 * 4661177 * 2
def baseEnd_4661177 : Nat := 2393424216682214857251143

theorem tailTrace_4661177 : CollatzResearch.WordTrace tailWord_4661177 prefixEnd_4661177 2393424216682214857251143 := by
  unfold tailWord_4661177
  simp only [CollatzResearch.WordTrace]
  refine ⟨170007091834359269498685785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113338061222906179665790523 170007091834359269498685785)
  ·
    refine ⟨127505318875769452124014339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170007091834359269498685785 127505318875769452124014339)
    ·
      refine ⟨191257978313654178186021509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127505318875769452124014339 191257978313654178186021509)
      ·
        refine ⟨35860870933810158409879033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191257978313654178186021509 35860870933810158409879033)
        ·
          refine ⟨26895653200357618807409275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35860870933810158409879033 26895653200357618807409275)
          ·
            refine ⟨40343479800536428211113913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26895653200357618807409275 40343479800536428211113913)
            ·
              refine ⟨30257609850402321158335435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40343479800536428211113913 30257609850402321158335435)
              ·
                refine ⟨45386414775603481737503153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30257609850402321158335435 45386414775603481737503153)
                ·
                  refine ⟨34039811081702611303127365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45386414775603481737503153 34039811081702611303127365)
                  ·
                    refine ⟨6382464577819239619336381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34039811081702611303127365 6382464577819239619336381)
                    ·
                      refine ⟨2393424216682214857251143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6382464577819239619336381 2393424216682214857251143)
                      ·
                        rfl

theorem cell23_4661177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4661177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661177 prefixEnd_4661177 := by exact prefixLift 4661177
  have htrace : WordTrace (prefixWord ++ tailWord_4661177) baseStart_4661177 baseEnd_4661177 := by
    simpa [prefixWord, tailWord_4661177, baseEnd_4661177] using wordTrace_append hprefix tailTrace_4661177
  have hstable : (prefixWord ++ tailWord_4661177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661177).length < 2 ^ (prefixWord ++ tailWord_4661177).sum := by decide
  have hdescent : baseEnd_4661177 < baseStart_4661177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661247 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_4661247 : Nat := 118140960795 + 4661247 * 2 ^ 59
def prefixEnd_4661247 : Nat := 4983230072969 + 3 ^ 40 * 4661247 * 2
def baseEnd_4661247 : Nat := 2393460160328029583375821

theorem tailTrace_4661247 : CollatzResearch.WordTrace tailWord_4661247 prefixEnd_4661247 2393460160328029583375821 := by
  unfold tailWord_4661247
  simp only [CollatzResearch.WordTrace]
  refine ⟨170009644944105671453733995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113339763296070447635822663 170009644944105671453733995)
  ·
    refine ⟨255014467416158507180600993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170009644944105671453733995 255014467416158507180600993)
    ·
      refine ⟨191260850562118880385450745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255014467416158507180600993 191260850562118880385450745)
      ·
        refine ⟨143445637921589160289088059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191260850562118880385450745 143445637921589160289088059)
        ·
          refine ⟨215168456882383740433632089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143445637921589160289088059 215168456882383740433632089)
          ·
            refine ⟨161376342661787805325224067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215168456882383740433632089 161376342661787805325224067)
            ·
              refine ⟨242064513992681707987836101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161376342661787805325224067 242064513992681707987836101)
              ·
                refine ⟨45387096373627820247719269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242064513992681707987836101 45387096373627820247719269)
                ·
                  refine ⟨8510080570055216296447363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45387096373627820247719269 8510080570055216296447363)
                  ·
                    refine ⟨12765120855082824444671045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8510080570055216296447363 12765120855082824444671045)
                    ·
                      refine ⟨2393460160328029583375821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12765120855082824444671045 2393460160328029583375821)
                      ·
                        rfl

theorem cell23_4661247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_4661247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661247 prefixEnd_4661247 := by exact prefixLift 4661247
  have htrace : WordTrace (prefixWord ++ tailWord_4661247) baseStart_4661247 baseEnd_4661247 := by
    simpa [prefixWord, tailWord_4661247, baseEnd_4661247] using wordTrace_append hprefix tailTrace_4661247
  have hstable : (prefixWord ++ tailWord_4661247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661247).length < 2 ^ (prefixWord ++ tailWord_4661247).sum := by decide
  have hdescent : baseEnd_4661247 < baseStart_4661247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661318 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4661318 : Nat := 118140960795 + 4661318 * 2 ^ 59
def prefixEnd_4661318 : Nat := 4983230072969 + 3 ^ 40 * 4661318 * 2
def baseEnd_4661318 : Nat := 2393496617454498805587995

theorem tailTrace_4661318 : CollatzResearch.WordTrace tailWord_4661318 prefixEnd_4661318 2393496617454498805587995 := by
  unfold tailWord_4661318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5312882328964014080611519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113341489684565633719712405 5312882328964014080611519)
  ·
    refine ⟨7969323493446021120917279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5312882328964014080611519 7969323493446021120917279)
    ·
      refine ⟨11953985240169031681375919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7969323493446021120917279 11953985240169031681375919)
      ·
        refine ⟨17930977860253547522063879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11953985240169031681375919 17930977860253547522063879)
        ·
          refine ⟨26896466790380321283095819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17930977860253547522063879 26896466790380321283095819)
          ·
            refine ⟨40344700185570481924643729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26896466790380321283095819 40344700185570481924643729)
            ·
              refine ⟨30258525139177861443482797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40344700185570481924643729 30258525139177861443482797)
              ·
                refine ⟨11346946927191698041306049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30258525139177861443482797 11346946927191698041306049)
                ·
                  refine ⟨8510210195393773530979537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11346946927191698041306049 8510210195393773530979537)
                  ·
                    refine ⟨6382657646545330148234653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8510210195393773530979537 6382657646545330148234653)
                    ·
                      refine ⟨2393496617454498805587995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6382657646545330148234653 2393496617454498805587995)
                      ·
                        rfl

theorem cell23_4661318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4661318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661318 prefixEnd_4661318 := by exact prefixLift 4661318
  have htrace : WordTrace (prefixWord ++ tailWord_4661318) baseStart_4661318 baseEnd_4661318 := by
    simpa [prefixWord, tailWord_4661318, baseEnd_4661318] using wordTrace_append hprefix tailTrace_4661318
  have hstable : (prefixWord ++ tailWord_4661318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661318).length < 2 ^ (prefixWord ++ tailWord_4661318).sum := by decide
  have hdescent : baseEnd_4661318 < baseStart_4661318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661342 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4661342 : Nat := 118140960795 + 4661342 * 2 ^ 59
def prefixEnd_4661342 : Nat := 4983230072969 + 3 ^ 40 * 4661342 * 2
def baseEnd_4661342 : Nat := 797836313663402237229295

theorem tailTrace_4661342 : CollatzResearch.WordTrace tailWord_4661342 prefixEnd_4661342 797836313663402237229295 := by
  unfold tailWord_4661342
  simp only [CollatzResearch.WordTrace]
  refine ⟨21251638734845187834805285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113342073252507668452294853 21251638734845187834805285)
  ·
    refine ⟨3984682262783472719025991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21251638734845187834805285 3984682262783472719025991)
    ·
      refine ⟨5977023394175209078538987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984682262783472719025991 5977023394175209078538987)
      ·
        refine ⟨8965535091262813617808481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977023394175209078538987 8965535091262813617808481)
        ·
          refine ⟨6724151318447110213356361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8965535091262813617808481 6724151318447110213356361)
          ·
            refine ⟨5043113488835332660017271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6724151318447110213356361 5043113488835332660017271)
            ·
              refine ⟨7564670233252998990025907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5043113488835332660017271 7564670233252998990025907)
              ·
                refine ⟨11347005349879498485038861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7564670233252998990025907 11347005349879498485038861)
                ·
                  refine ⟨4255127006204811931889573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11347005349879498485038861 4255127006204811931889573)
                  ·
                    refine ⟨797836313663402237229295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4255127006204811931889573 797836313663402237229295)
                    ·
                      rfl

theorem cell23_4661342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4661342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661342 prefixEnd_4661342 := by exact prefixLift 4661342
  have htrace : WordTrace (prefixWord ++ tailWord_4661342) baseStart_4661342 baseEnd_4661342 := by
    simpa [prefixWord, tailWord_4661342, baseEnd_4661342] using wordTrace_append hprefix tailTrace_4661342
  have hstable : (prefixWord ++ tailWord_4661342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661342).length < 2 ^ (prefixWord ++ tailWord_4661342).sum := by decide
  have hdescent : baseEnd_4661342 < baseStart_4661342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661348 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_4661348 : Nat := 118140960795 + 4661348 * 2 ^ 59
def prefixEnd_4661348 : Nat := 4983230072969 + 3 ^ 40 * 4661348 * 2
def baseEnd_4661348 : Nat := 2393512021874133688212857

theorem tailTrace_4661348 : CollatzResearch.WordTrace tailWord_4661348 prefixEnd_4661348 2393512021874133688212857 := by
  unfold tailWord_4661348
  simp only [CollatzResearch.WordTrace]
  refine ⟨85006664358369882851580349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113342219144493177135440465 85006664358369882851580349)
  ·
    refine ⟨31877499134388706069342631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85006664358369882851580349 31877499134388706069342631)
    ·
      refine ⟨47816248701583059104013947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31877499134388706069342631 47816248701583059104013947)
      ·
        refine ⟨71724373052374588656020921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47816248701583059104013947 71724373052374588656020921)
        ·
          refine ⟨53793279789280941492015691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71724373052374588656020921 53793279789280941492015691)
          ·
            refine ⟨80689919683921412238023537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53793279789280941492015691 80689919683921412238023537)
            ·
              refine ⟨60517439762941059178517653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80689919683921412238023537 60517439762941059178517653)
              ·
                refine ⟨2836754988887862148993015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60517439762941059178517653 2836754988887862148993015)
                ·
                  refine ⟨4255132483331793223489523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836754988887862148993015 4255132483331793223489523)
                  ·
                    refine ⟨6382698724997689835234285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4255132483331793223489523 6382698724997689835234285)
                    ·
                      refine ⟨2393512021874133688212857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6382698724997689835234285 2393512021874133688212857)
                      ·
                        rfl

theorem cell23_4661348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_4661348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661348 prefixEnd_4661348 := by exact prefixLift 4661348
  have htrace : WordTrace (prefixWord ++ tailWord_4661348) baseStart_4661348 baseEnd_4661348 := by
    simpa [prefixWord, tailWord_4661348, baseEnd_4661348] using wordTrace_append hprefix tailTrace_4661348
  have hstable : (prefixWord ++ tailWord_4661348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661348).length < 2 ^ (prefixWord ++ tailWord_4661348).sum := by decide
  have hdescent : baseEnd_4661348 < baseStart_4661348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661399 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 1, 1, 3]
def baseStart_4661399 : Nat := 118140960795 + 4661399 * 2 ^ 59
def prefixEnd_4661399 : Nat := 4983230072969 + 3 ^ 40 * 4661399 * 2
def baseEnd_4661399 : Nat := 2393538209387512988675123

theorem tailTrace_4661399 : CollatzResearch.WordTrace tailWord_4661399 prefixEnd_4661399 2393538209387512988675123 := by
  unfold tailWord_4661399
  simp only [CollatzResearch.WordTrace]
  refine ⟨170015188839555001413267251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113343459226370000942178167 170015188839555001413267251)
  ·
    refine ⟨255022783259332502119900877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170015188839555001413267251 255022783259332502119900877)
    ·
      refine ⟨95633543722249688294962829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255022783259332502119900877 95633543722249688294962829)
      ·
        refine ⟨35862578895843633110611061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95633543722249688294962829 35862578895843633110611061)
        ·
          refine ⟨3362116771485340604119787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35862578895843633110611061 3362116771485340604119787)
          ·
            refine ⟨5043175157228010906179681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362116771485340604119787 5043175157228010906179681)
            ·
              refine ⟨3782381367921008179634761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5043175157228010906179681 3782381367921008179634761)
              ·
                refine ⟨2836786025940756134726071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3782381367921008179634761 2836786025940756134726071)
                ·
                  refine ⟨4255179038911134202089107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836786025940756134726071 4255179038911134202089107)
                  ·
                    refine ⟨6382768558366701303133661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4255179038911134202089107 6382768558366701303133661)
                    ·
                      refine ⟨2393538209387512988675123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6382768558366701303133661 2393538209387512988675123)
                      ·
                        rfl

theorem cell23_4661399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_4661399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661399 prefixEnd_4661399 := by exact prefixLift 4661399
  have htrace : WordTrace (prefixWord ++ tailWord_4661399) baseStart_4661399 baseEnd_4661399 := by
    simpa [prefixWord, tailWord_4661399, baseEnd_4661399] using wordTrace_append hprefix tailTrace_4661399
  have hstable : (prefixWord ++ tailWord_4661399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661399).length < 2 ^ (prefixWord ++ tailWord_4661399).sum := by decide
  have hdescent : baseEnd_4661399 < baseStart_4661399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661442 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4661442 : Nat := 118140960795 + 4661442 * 2 ^ 59
def prefixEnd_4661442 : Nat := 4983230072969 + 3 ^ 40 * 4661442 * 2
def baseEnd_4661442 : Nat := 2393560289055656320437425

theorem tailTrace_4661442 : CollatzResearch.WordTrace tailWord_4661442 prefixEnd_4661442 2393560289055656320437425 := by
  unfold tailWord_4661442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42504189294599804939270645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113344504785599479838055053 42504189294599804939270645)
  ·
    refine ⟨3984767746368731713056623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42504189294599804939270645 3984767746368731713056623)
    ·
      refine ⟨5977151619553097569584935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984767746368731713056623 5977151619553097569584935)
      ·
        refine ⟨8965727429329646354377403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977151619553097569584935 8965727429329646354377403)
        ·
          refine ⟨13448591143994469531566105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8965727429329646354377403 13448591143994469531566105)
          ·
            refine ⟨10086443357995852148674579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13448591143994469531566105 10086443357995852148674579)
            ·
              refine ⟨15129665036993778223011869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10086443357995852148674579 15129665036993778223011869)
              ·
                refine ⟨5673624388872666833629451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15129665036993778223011869 5673624388872666833629451)
                ·
                  refine ⟨8510436583309000250444177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5673624388872666833629451 8510436583309000250444177)
                  ·
                    refine ⟨6382827437481750187833133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8510436583309000250444177 6382827437481750187833133)
                    ·
                      refine ⟨2393560289055656320437425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6382827437481750187833133 2393560289055656320437425)
                      ·
                        rfl

theorem cell23_4661442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4661442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661442 prefixEnd_4661442 := by exact prefixLift 4661442
  have htrace : WordTrace (prefixWord ++ tailWord_4661442) baseStart_4661442 baseEnd_4661442 := by
    simpa [prefixWord, tailWord_4661442, baseEnd_4661442] using wordTrace_append hprefix tailTrace_4661442
  have hstable : (prefixWord ++ tailWord_4661442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661442).length < 2 ^ (prefixWord ++ tailWord_4661442).sum := by decide
  have hdescent : baseEnd_4661442 < baseStart_4661442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661484 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 7]
def baseStart_4661484 : Nat := 118140960795 + 4661484 * 2 ^ 59
def prefixEnd_4661484 : Nat := 4983230072969 + 3 ^ 40 * 4661484 * 2
def baseEnd_4661484 : Nat := 265953539471460572901359

theorem tailTrace_4661484 : CollatzResearch.WordTrace tailWord_4661484 prefixEnd_4661484 265953539471460572901359 := by
  unfold tailWord_4661484
  simp only [CollatzResearch.WordTrace]
  refine ⟨85009144522123530465055753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113345526029498040620074337 85009144522123530465055753)
  ·
    refine ⟨63756858391592647848791815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85009144522123530465055753 63756858391592647848791815)
    ·
      refine ⟨95635287587388971773187723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63756858391592647848791815 95635287587388971773187723)
      ·
        refine ⟨143452931381083457659781585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95635287587388971773187723 143452931381083457659781585)
        ·
          refine ⟨107589698535812593244836189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143452931381083457659781585 107589698535812593244836189)
          ·
            refine ⟨40346136950929722466813571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107589698535812593244836189 40346136950929722466813571)
            ·
              refine ⟨60519205426394583700220357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40346136950929722466813571 60519205426394583700220357)
              ·
                refine ⟨11347351017448984443791317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60519205426394583700220357 11347351017448984443791317)
                ·
                  refine ⟨265953539471460572901359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11347351017448984443791317 265953539471460572901359)
                  ·
                    rfl

theorem cell23_4661484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_4661484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661484 prefixEnd_4661484 := by exact prefixLift 4661484
  have htrace : WordTrace (prefixWord ++ tailWord_4661484) baseStart_4661484 baseEnd_4661484 := by
    simpa [prefixWord, tailWord_4661484, baseEnd_4661484] using wordTrace_append hprefix tailTrace_4661484
  have hstable : (prefixWord ++ tailWord_4661484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661484).length < 2 ^ (prefixWord ++ tailWord_4661484).sum := by decide
  have hdescent : baseEnd_4661484 < baseStart_4661484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661551 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_4661551 : Nat := 118140960795 + 4661551 * 2 ^ 59
def prefixEnd_4661551 : Nat := 4983230072969 + 3 ^ 40 * 4661551 * 2
def baseEnd_4661551 : Nat := 2393616258446996393974423

theorem tailTrace_4661551 : CollatzResearch.WordTrace tailWord_4661551 prefixEnd_4661551 2393616258446996393974423 := by
  unfold tailWord_4661551
  simp only [CollatzResearch.WordTrace]
  refine ⟨170020732735004331372800507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113347155156669554248533671 170020732735004331372800507)
  ·
    refine ⟨255031099102506497059200761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170020732735004331372800507 255031099102506497059200761)
    ·
      refine ⟨191273324326879872794400571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255031099102506497059200761 191273324326879872794400571)
      ·
        refine ⟨286909986490319809191600857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191273324326879872794400571 286909986490319809191600857)
        ·
          refine ⟨215182489867739856893700643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286909986490319809191600857 215182489867739856893700643)
          ·
            refine ⟨322773734801609785340550965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215182489867739856893700643 322773734801609785340550965)
            ·
              refine ⟨30260037637650917375676653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322773734801609785340550965 30260037637650917375676653)
              ·
                refine ⟨11347514114119094015878745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30260037637650917375676653 11347514114119094015878745)
                ·
                  refine ⟨8510635585589320511909059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11347514114119094015878745 8510635585589320511909059)
                  ·
                    refine ⟨12765953378383980767863589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8510635585589320511909059 12765953378383980767863589)
                    ·
                      refine ⟨2393616258446996393974423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12765953378383980767863589 2393616258446996393974423)
                      ·
                        rfl

theorem cell23_4661551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_4661551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661551 prefixEnd_4661551 := by exact prefixLift 4661551
  have htrace : WordTrace (prefixWord ++ tailWord_4661551) baseStart_4661551 baseEnd_4661551 := by
    simpa [prefixWord, tailWord_4661551, baseEnd_4661551] using wordTrace_append hprefix tailTrace_4661551
  have hstable : (prefixWord ++ tailWord_4661551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661551).length < 2 ^ (prefixWord ++ tailWord_4661551).sum := by decide
  have hdescent : baseEnd_4661551 < baseStart_4661551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661569 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 5]
def baseStart_4661569 : Nat := 118140960795 + 4661569 * 2 ^ 59
def prefixEnd_4661569 : Nat := 4983230072969 + 3 ^ 40 * 4661569 * 2
def baseEnd_4661569 : Nat := 265958389010975258172149

theorem tailTrace_4661569 : CollatzResearch.WordTrace tailWord_4661569 prefixEnd_4661569 265958389010975258172149 := by
  unfold tailWord_4661569
  simp only [CollatzResearch.WordTrace]
  refine ⟨170021389248939120446955761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113347592832626080297970507 170021389248939120446955761)
  ·
    refine ⟨127516041936704340335216821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170021389248939120446955761 127516041936704340335216821)
    ·
      refine ⟨11954628931566031906426577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127516041936704340335216821 11954628931566031906426577)
      ·
        refine ⟨8965971698674523929819933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11954628931566031906426577 8965971698674523929819933)
        ·
          refine ⟨3362239387002946473682475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8965971698674523929819933 3362239387002946473682475)
          ·
            refine ⟨5043359080504419710523713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362239387002946473682475 5043359080504419710523713)
            ·
              refine ⟨3782519310378314782892785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5043359080504419710523713 3782519310378314782892785)
              ·
                refine ⟨2836889482783736087169589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3782519310378314782892785 2836889482783736087169589)
                ·
                  refine ⟨265958389010975258172149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2836889482783736087169589 265958389010975258172149)
                  ·
                    rfl

theorem cell23_4661569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 5].length) (baseStart_4661569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661569 prefixEnd_4661569 := by exact prefixLift 4661569
  have htrace : WordTrace (prefixWord ++ tailWord_4661569) baseStart_4661569 baseEnd_4661569 := by
    simpa [prefixWord, tailWord_4661569, baseEnd_4661569] using wordTrace_append hprefix tailTrace_4661569
  have hstable : (prefixWord ++ tailWord_4661569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661569).length < 2 ^ (prefixWord ++ tailWord_4661569).sum := by decide
  have hdescent : baseEnd_4661569 < baseStart_4661569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661591 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 6]
def baseStart_4661591 : Nat := 118140960795 + 4661591 * 2 ^ 59
def prefixEnd_4661591 : Nat := 4983230072969 + 3 ^ 40 * 4661591 * 2
def baseEnd_4661591 : Nat := 265959644185908470830471

theorem tailTrace_4661591 : CollatzResearch.WordTrace tailWord_4661591 prefixEnd_4661591 265959644185908470830471 := by
  unfold tailWord_4661591
  simp only [CollatzResearch.WordTrace]
  refine ⟨170022191654859418204256627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113348127769906278802837751 170022191654859418204256627)
  ·
    refine ⟨255033287482289127306384941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170022191654859418204256627 255033287482289127306384941)
    ·
      refine ⟨95637482805858422739894353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255033287482289127306384941 95637482805858422739894353)
      ·
        refine ⟨71728112104393817054920765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95637482805858422739894353 71728112104393817054920765)
        ·
          refine ⟨26898042039147681395595287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71728112104393817054920765 26898042039147681395595287)
          ·
            refine ⟨40347063058721522093392931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26898042039147681395595287 40347063058721522093392931)
            ·
              refine ⟨60520594588082283140089397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40347063058721522093392931 60520594588082283140089397)
              ·
                refine ⟨5673805742632714044383381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60520594588082283140089397 5673805742632714044383381)
                ·
                  refine ⟨265959644185908470830471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5673805742632714044383381 265959644185908470830471)
                  ·
                    rfl

theorem cell23_4661591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 6].length) (baseStart_4661591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661591 prefixEnd_4661591 := by exact prefixLift 4661591
  have htrace : WordTrace (prefixWord ++ tailWord_4661591) baseStart_4661591 baseEnd_4661591 := by
    simpa [prefixWord, tailWord_4661591, baseEnd_4661591] using wordTrace_append hprefix tailTrace_4661591
  have hstable : (prefixWord ++ tailWord_4661591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661591).length < 2 ^ (prefixWord ++ tailWord_4661591).sum := by decide
  have hdescent : baseEnd_4661591 < baseStart_4661591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661605 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_4661605 : Nat := 118140960795 + 4661605 * 2 ^ 59
def prefixEnd_4661605 : Nat := 4983230072969 + 3 ^ 40 * 4661605 * 2
def baseEnd_4661605 : Nat := 2393643986402339182699175

theorem tailTrace_4661605 : CollatzResearch.WordTrace tailWord_4661605 prefixEnd_4661605 2393643986402339182699175 := by
  unfold tailWord_4661605
  simp only [CollatzResearch.WordTrace]
  refine ⟨170022702276808698595266269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113348468184539132396844179 170022702276808698595266269)
  ·
    refine ⟨63758513353803261973224851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170022702276808698595266269 63758513353803261973224851)
    ·
      refine ⟨95637770030704892959837277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63758513353803261973224851 95637770030704892959837277)
      ·
        refine ⟨35864163761514334859938979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95637770030704892959837277 35864163761514334859938979)
        ·
          refine ⟨53796245642271502289908469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35864163761514334859938979 53796245642271502289908469)
          ·
            refine ⟨5043398028962953339678919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53796245642271502289908469 5043398028962953339678919)
            ·
              refine ⟨7565097043444430009518379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5043398028962953339678919 7565097043444430009518379)
              ·
                refine ⟨11347645565166645014277569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7565097043444430009518379 11347645565166645014277569)
                ·
                  refine ⟨8510734173874983760708177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11347645565166645014277569 8510734173874983760708177)
                  ·
                    refine ⟨6383050630406237820531133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8510734173874983760708177 6383050630406237820531133)
                    ·
                      refine ⟨2393643986402339182699175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383050630406237820531133 2393643986402339182699175)
                      ·
                        rfl

theorem cell23_4661605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_4661605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661605 prefixEnd_4661605 := by exact prefixLift 4661605
  have htrace : WordTrace (prefixWord ++ tailWord_4661605) baseStart_4661605 baseEnd_4661605 := by
    simpa [prefixWord, tailWord_4661605, baseEnd_4661605] using wordTrace_append hprefix tailTrace_4661605
  have hstable : (prefixWord ++ tailWord_4661605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661605).length < 2 ^ (prefixWord ++ tailWord_4661605).sum := by decide
  have hdescent : baseEnd_4661605 < baseStart_4661605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661612 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_4661612 : Nat := 118140960795 + 4661612 * 2 ^ 59
def prefixEnd_4661612 : Nat := 4983230072969 + 3 ^ 40 * 4661612 * 2
def baseEnd_4661612 : Nat := 797882526922306885103881

theorem tailTrace_4661612 : CollatzResearch.WordTrace tailWord_4661612 prefixEnd_4661612 797882526922306885103881 := by
  unfold tailWord_4661612
  simp only [CollatzResearch.WordTrace]
  refine ⟨85011478793891669395385545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113348638391855559193847393 85011478793891669395385545)
  ·
    refine ⟨63758609095418752046539159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85011478793891669395385545 63758609095418752046539159)
    ·
      refine ⟨95637913643128128069808739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63758609095418752046539159 95637913643128128069808739)
      ·
        refine ⟨143456870464692192104713109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95637913643128128069808739 143456870464692192104713109)
        ·
          refine ⟨6724540803032446504908427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143456870464692192104713109 6724540803032446504908427)
          ·
            refine ⟨10086811204548669757362641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724540803032446504908427 10086811204548669757362641)
            ·
              refine ⟨7565108403411502318021981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10086811204548669757362641 7565108403411502318021981)
              ·
                refine ⟨2836915651279313369258243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7565108403411502318021981 2836915651279313369258243)
                ·
                  refine ⟨4255373476918970053887365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836915651279313369258243 4255373476918970053887365)
                  ·
                    refine ⟨797882526922306885103881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4255373476918970053887365 797882526922306885103881)
                    ·
                      rfl

theorem cell23_4661612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_4661612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661612 prefixEnd_4661612 := by exact prefixLift 4661612
  have htrace : WordTrace (prefixWord ++ tailWord_4661612) baseStart_4661612 baseEnd_4661612 := by
    simpa [prefixWord, tailWord_4661612, baseEnd_4661612] using wordTrace_append hprefix tailTrace_4661612
  have hstable : (prefixWord ++ tailWord_4661612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661612).length < 2 ^ (prefixWord ++ tailWord_4661612).sum := by decide
  have hdescent : baseEnd_4661612 < baseStart_4661612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661642 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_4661642 : Nat := 118140960795 + 4661642 * 2 ^ 59
def prefixEnd_4661642 : Nat := 4983230072969 + 3 ^ 40 * 4661642 * 2
def baseEnd_4661642 : Nat := 265962553909617281992945

theorem tailTrace_4661642 : CollatzResearch.WordTrace tailWord_4661642 prefixEnd_4661642 265962553909617281992945 := by
  unfold tailWord_4661642
  simp only [CollatzResearch.WordTrace]
  refine ⟨42506012944418663478590795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113349367851783102609575453 42506012944418663478590795)
  ·
    refine ⟨63759019416627995217886193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42506012944418663478590795 63759019416627995217886193)
    ·
      refine ⟨47819264562470996413414645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63759019416627995217886193 47819264562470996413414645)
      ·
        refine ⟨4483056052731655913757623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47819264562470996413414645 4483056052731655913757623)
        ·
          refine ⟨6724584079097483870636435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4483056052731655913757623 6724584079097483870636435)
          ·
            refine ⟨10086876118646225805954653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724584079097483870636435 10086876118646225805954653)
            ·
              refine ⟨3782578544492334677232995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10086876118646225805954653 3782578544492334677232995)
              ·
                refine ⟨5673867816738502015849493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3782578544492334677232995 5673867816738502015849493)
                ·
                  refine ⟨265962553909617281992945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5673867816738502015849493 265962553909617281992945)
                  ·
                    rfl

theorem cell23_4661642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_4661642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661642 prefixEnd_4661642 := by exact prefixLift 4661642
  have htrace : WordTrace (prefixWord ++ tailWord_4661642) baseStart_4661642 baseEnd_4661642 := by
    simpa [prefixWord, tailWord_4661642, baseEnd_4661642] using wordTrace_append hprefix tailTrace_4661642
  have hstable : (prefixWord ++ tailWord_4661642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661642).length < 2 ^ (prefixWord ++ tailWord_4661642).sum := by decide
  have hdescent : baseEnd_4661642 < baseStart_4661642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661662 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4661662 : Nat := 118140960795 + 4661662 * 2 ^ 59
def prefixEnd_4661662 : Nat := 4983230072969 + 3 ^ 40 * 4661662 * 2
def baseEnd_4661662 : Nat := 2393673254799645459686413

theorem tailTrace_4661662 : CollatzResearch.WordTrace tailWord_4661662 prefixEnd_4661662 2393673254799645459686413 := by
  unfold tailWord_4661662
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253097654700274666261405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113349854158401464886727493 21253097654700274666261405)
  ·
    refine ⟨7969911620512602999848027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21253097654700274666261405 7969911620512602999848027)
    ·
      refine ⟨11954867430768904499772041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7969911620512602999848027 11954867430768904499772041)
      ·
        refine ⟨8966150573076678374829031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11954867430768904499772041 8966150573076678374829031)
        ·
          refine ⟨13449225859615017562243547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8966150573076678374829031 13449225859615017562243547)
          ·
            refine ⟨20173838789422526343365321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13449225859615017562243547 20173838789422526343365321)
            ·
              refine ⟨15130379092066894757523991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20173838789422526343365321 15130379092066894757523991)
              ·
                refine ⟨22695568638100342136285987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15130379092066894757523991 22695568638100342136285987)
                ·
                  refine ⟨34043352957150513204428981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22695568638100342136285987 34043352957150513204428981)
                  ·
                    refine ⟨3191564339732860612915217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34043352957150513204428981 3191564339732860612915217)
                    ·
                      refine ⟨2393673254799645459686413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191564339732860612915217 2393673254799645459686413)
                      ·
                        rfl

theorem cell23_4661662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4661662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661662 prefixEnd_4661662 := by exact prefixLift 4661662
  have htrace : WordTrace (prefixWord ++ tailWord_4661662) baseStart_4661662 baseEnd_4661662 := by
    simpa [prefixWord, tailWord_4661662, baseEnd_4661662] using wordTrace_append hprefix tailTrace_4661662
  have hstable : (prefixWord ++ tailWord_4661662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661662).length < 2 ^ (prefixWord ++ tailWord_4661662).sum := by decide
  have hdescent : baseEnd_4661662 < baseStart_4661662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
