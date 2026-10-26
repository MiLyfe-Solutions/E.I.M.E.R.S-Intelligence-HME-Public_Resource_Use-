import V185TrunkScan23Chunk0500

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2963508 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2963508 : Nat := 118140960795 + 2963508 * 2 ^ 59
def prefixEnd_2963508 : Nat := 4983230072969 + 3 ^ 40 * 2963508 * 2
def baseEnd_2963508 : Nat := 169078225271610721669009

theorem tailTrace_2963508 : CollatzResearch.WordTrace tailWord_2963508 prefixEnd_2963508 169078225271610721669009 := by
  unfold tailWord_2963508
  simp only [CollatzResearch.WordTrace]
  refine ⟨54044008273862058858345589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72058677698482745144460785 54044008273862058858345589)
  ·
    refine ⟨5066625775674568017969899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54044008273862058858345589 5066625775674568017969899)
    ·
      refine ⟨7599938663511852026954849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5066625775674568017969899 7599938663511852026954849)
      ·
        refine ⟨5699953997633889020216137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7599938663511852026954849 5699953997633889020216137)
        ·
          refine ⟨4274965498225416765162103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699953997633889020216137 4274965498225416765162103)
          ·
            refine ⟨6412448247338125147743155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274965498225416765162103 6412448247338125147743155)
            ·
              refine ⟨9618672371007187721614733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412448247338125147743155 9618672371007187721614733)
              ·
                refine ⟨3607002139127695395605525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9618672371007187721614733 3607002139127695395605525)
                ·
                  refine ⟨169078225271610721669009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3607002139127695395605525 169078225271610721669009)
                  ·
                    rfl

theorem cell23_2963508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2963508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963508 prefixEnd_2963508 := by exact prefixLift 2963508
  have htrace : WordTrace (prefixWord ++ tailWord_2963508) baseStart_2963508 baseEnd_2963508 := by
    simpa [prefixWord, tailWord_2963508, baseEnd_2963508] using wordTrace_append hprefix tailTrace_2963508
  have hstable : (prefixWord ++ tailWord_2963508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963508).length < 2 ^ (prefixWord ++ tailWord_2963508).sum := by decide
  have hdescent : baseEnd_2963508 < baseStart_2963508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963521 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2963521 : Nat := 118140960795 + 2963521 * 2 ^ 59
def prefixEnd_2963521 : Nat := 4983230072969 + 3 ^ 40 * 2963521 * 2
def baseEnd_2963521 : Nat := 507236900897668314719507

theorem tailTrace_2963521 : CollatzResearch.WordTrace tailWord_2963521 prefixEnd_2963521 507236900897668314719507 := by
  unfold tailWord_2963521
  simp only [CollatzResearch.WordTrace]
  refine ⟨108088490696677020936914417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72058993797784680624609611 108088490696677020936914417)
  ·
    refine ⟨81066368022507765702685813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108088490696677020936914417 81066368022507765702685813)
    ·
      refine ⟨7599972002110103034626795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81066368022507765702685813 7599972002110103034626795)
      ·
        refine ⟨11399958003165154551940193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7599972002110103034626795 11399958003165154551940193)
        ·
          refine ⟨8549968502373865913955145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11399958003165154551940193 8549968502373865913955145)
          ·
            refine ⟨6412476376780399435466359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8549968502373865913955145 6412476376780399435466359)
            ·
              refine ⟨9618714565170599153199539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412476376780399435466359 9618714565170599153199539)
              ·
                refine ⟨14428071847755898729799309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618714565170599153199539 14428071847755898729799309)
                ·
                  refine ⟨5410526942908462023674741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14428071847755898729799309 5410526942908462023674741)
                  ·
                    refine ⟨507236900897668314719507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5410526942908462023674741 507236900897668314719507)
                    ·
                      rfl

theorem cell23_2963521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2963521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963521 prefixEnd_2963521 := by exact prefixLift 2963521
  have htrace : WordTrace (prefixWord ++ tailWord_2963521) baseStart_2963521 baseEnd_2963521 := by
    simpa [prefixWord, tailWord_2963521, baseEnd_2963521] using wordTrace_append hprefix tailTrace_2963521
  have hstable : (prefixWord ++ tailWord_2963521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963521).length < 2 ^ (prefixWord ++ tailWord_2963521).sum := by decide
  have hdescent : baseEnd_2963521 < baseStart_2963521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963534 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2963534 : Nat := 118140960795 + 2963534 * 2 ^ 59
def prefixEnd_2963534 : Nat := 4983230072969 + 3 ^ 40 * 2963534 * 2
def baseEnd_2963534 : Nat := 507239125980504464431987

theorem tailTrace_2963534 : CollatzResearch.WordTrace tailWord_2963534 prefixEnd_2963534 507239125980504464431987 := by
  unfold tailWord_2963534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511120605703740519642207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72059309897086616104758437 13511120605703740519642207)
  ·
    refine ⟨20266680908555610779463311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13511120605703740519642207 20266680908555610779463311)
    ·
      refine ⟨30400021362833416169194967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20266680908555610779463311 30400021362833416169194967)
      ·
        refine ⟨45600032044250124253792451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30400021362833416169194967 45600032044250124253792451)
        ·
          refine ⟨68400048066375186380688677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45600032044250124253792451 68400048066375186380688677)
          ·
            refine ⟨12825009012445347446379127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68400048066375186380688677 12825009012445347446379127)
            ·
              refine ⟨19237513518668021169568691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12825009012445347446379127 19237513518668021169568691)
              ·
                refine ⟨28856270278002031754353037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19237513518668021169568691 28856270278002031754353037)
                ·
                  refine ⟨10821101354250761907882389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28856270278002031754353037 10821101354250761907882389)
                  ·
                    refine ⟨507239125980504464431987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10821101354250761907882389 507239125980504464431987)
                    ·
                      rfl

theorem cell23_2963534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2963534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963534 prefixEnd_2963534 := by exact prefixLift 2963534
  have htrace : WordTrace (prefixWord ++ tailWord_2963534) baseStart_2963534 baseEnd_2963534 := by
    simpa [prefixWord, tailWord_2963534, baseEnd_2963534] using wordTrace_append hprefix tailTrace_2963534
  have hstable : (prefixWord ++ tailWord_2963534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963534).length < 2 ^ (prefixWord ++ tailWord_2963534).sum := by decide
  have hdescent : baseEnd_2963534 < baseStart_2963534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963552 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 1, 1, 3]
def baseStart_2963552 : Nat := 118140960795 + 2963552 * 2 ^ 59
def prefixEnd_2963552 : Nat := 4983230072969 + 3 ^ 40 * 2963552 * 2
def baseEnd_2963552 : Nat := 1521726620593294322870879

theorem tailTrace_2963552 : CollatzResearch.WordTrace tailWord_2963552 prefixEnd_2963552 1521726620593294322870879 := by
  unfold tailWord_2963552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54044810679782356615646455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72059747573043142154195273 54044810679782356615646455)
  ·
    refine ⟨81067216019673534923469683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54044810679782356615646455 81067216019673534923469683)
    ·
      refine ⟨121600824029510302385204525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81067216019673534923469683 121600824029510302385204525)
      ·
        refine ⟨45600309011066363394451697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121600824029510302385204525 45600309011066363394451697)
        ·
          refine ⟨34200231758299772545838773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45600309011066363394451697 34200231758299772545838773)
          ·
            refine ⟨3206271727340603676172385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34200231758299772545838773 3206271727340603676172385)
            ·
              refine ⟨2404703795505452757129289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206271727340603676172385 2404703795505452757129289)
              ·
                refine ⟨1803527846629089567846967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404703795505452757129289 1803527846629089567846967)
                ·
                  refine ⟨2705291769943634351770451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803527846629089567846967 2705291769943634351770451)
                  ·
                    refine ⟨4057937654915451527655677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705291769943634351770451 4057937654915451527655677)
                    ·
                      refine ⟨1521726620593294322870879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057937654915451527655677 1521726620593294322870879)
                      ·
                        rfl

theorem cell23_2963552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_2963552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963552 prefixEnd_2963552 := by exact prefixLift 2963552
  have htrace : WordTrace (prefixWord ++ tailWord_2963552) baseStart_2963552 baseEnd_2963552 := by
    simpa [prefixWord, tailWord_2963552, baseEnd_2963552] using wordTrace_append hprefix tailTrace_2963552
  have hstable : (prefixWord ++ tailWord_2963552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963552).length < 2 ^ (prefixWord ++ tailWord_2963552).sum := by decide
  have hdescent : baseEnd_2963552 < baseStart_2963552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963564 : List Nat := [2, 2, 1, 1, 3, 3, 3, 8]
def baseStart_2963564 : Nat := 118140960795 + 2963564 * 2 ^ 59
def prefixEnd_2963564 : Nat := 4983230072969 + 3 ^ 40 * 2963564 * 2
def baseEnd_2963564 : Nat := 56360473420783269478549

theorem tailTrace_2963564 : CollatzResearch.WordTrace tailWord_2963564 prefixEnd_2963564 56360473420783269478549 := by
  unfold tailWord_2963564
  simp only [CollatzResearch.WordTrace]
  refine ⟨54045029517760619640364873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72060039357014159520486497 54045029517760619640364873)
  ·
    refine ⟨40533772138320464730273655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54045029517760619640364873 40533772138320464730273655)
    ·
      refine ⟨60800658207480697095410483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40533772138320464730273655 60800658207480697095410483)
      ·
        refine ⟨91200987311221045643115725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60800658207480697095410483 91200987311221045643115725)
        ·
          refine ⟨34200370241707892116168397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91200987311221045643115725 34200370241707892116168397)
          ·
            refine ⟨12825138840640459543563149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34200370241707892116168397 12825138840640459543563149)
            ·
              refine ⟨4809427065240172328836181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12825138840640459543563149 4809427065240172328836181)
              ·
                refine ⟨56360473420783269478549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4809427065240172328836181 56360473420783269478549)
                ·
                  rfl

theorem cell23_2963564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 8].length) (baseStart_2963564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963564 prefixEnd_2963564 := by exact prefixLift 2963564
  have htrace : WordTrace (prefixWord ++ tailWord_2963564) baseStart_2963564 baseEnd_2963564 := by
    simpa [prefixWord, tailWord_2963564, baseEnd_2963564] using wordTrace_append hprefix tailTrace_2963564
  have hstable : (prefixWord ++ tailWord_2963564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963564).length < 2 ^ (prefixWord ++ tailWord_2963564).sum := by decide
  have hdescent : baseEnd_2963564 < baseStart_2963564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963581 : List Nat := [1, 4, 1, 1, 3, 3, 3, 7]
def baseStart_2963581 : Nat := 118140960795 + 2963581 * 2 ^ 59
def prefixEnd_2963581 : Nat := 4983230072969 + 3 ^ 40 * 2963581 * 2
def baseEnd_2963581 : Nat := 56360796723417581829935

theorem tailTrace_2963581 : CollatzResearch.WordTrace tailWord_2963581 prefixEnd_2963581 56360796723417581829935 := by
  unfold tailWord_2963581
  simp only [CollatzResearch.WordTrace]
  refine ⟨108090679076459651184098597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72060452717639767456065731 108090679076459651184098597)
  ·
    refine ⟨20267002326836184597018487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108090679076459651184098597 20267002326836184597018487)
    ·
      refine ⟨30400503490254276895527731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20267002326836184597018487 30400503490254276895527731)
      ·
        refine ⟨45600755235381415343291597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30400503490254276895527731 45600755235381415343291597)
        ·
          refine ⟨17100283213268030753734349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45600755235381415343291597 17100283213268030753734349)
          ·
            refine ⟨6412606204975511532650381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17100283213268030753734349 6412606204975511532650381)
            ·
              refine ⟨2404727326865816824743893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6412606204975511532650381 2404727326865816824743893)
              ·
                refine ⟨56360796723417581829935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2404727326865816824743893 56360796723417581829935)
                ·
                  rfl

theorem cell23_2963581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 7].length) (baseStart_2963581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963581 prefixEnd_2963581 := by exact prefixLift 2963581
  have htrace : WordTrace (prefixWord ++ tailWord_2963581) baseStart_2963581 baseEnd_2963581 := by
    simpa [prefixWord, tailWord_2963581, baseEnd_2963581] using wordTrace_append hprefix tailTrace_2963581
  have hstable : (prefixWord ++ tailWord_2963581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963581).length < 2 ^ (prefixWord ++ tailWord_2963581).sum := by decide
  have hdescent : baseEnd_2963581 < baseStart_2963581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963591 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_2963591 : Nat := 118140960795 + 2963591 * 2 ^ 59
def prefixEnd_2963591 : Nat := 4983230072969 + 3 ^ 40 * 2963591 * 2
def baseEnd_2963591 : Nat := 1521746646338819670283199

theorem tailTrace_2963591 : CollatzResearch.WordTrace tailWord_2963591 prefixEnd_2963591 1521746646338819670283199 := by
  unfold tailWord_2963591
  simp only [CollatzResearch.WordTrace]
  refine ⟨108091043806423422891962627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72060695870948948594641751 108091043806423422891962627)
  ·
    refine ⟨162136565709635134337943941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108091043806423422891962627 162136565709635134337943941)
    ·
      refine ⟨30400606070556587688364489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162136565709635134337943941 30400606070556587688364489)
      ·
        refine ⟨22800454552917440766273367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30400606070556587688364489 22800454552917440766273367)
        ·
          refine ⟨34200681829376161149410051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22800454552917440766273367 34200681829376161149410051)
          ·
            refine ⟨51301022744064241724115077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34200681829376161149410051 51301022744064241724115077)
            ·
              refine ⟨9618941764512045323271577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51301022744064241724115077 9618941764512045323271577)
              ·
                refine ⟨7214206323384033992453683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9618941764512045323271577 7214206323384033992453683)
                ·
                  refine ⟨10821309485076050988680525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214206323384033992453683 10821309485076050988680525)
                  ·
                    refine ⟨4057991056903519120755197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10821309485076050988680525 4057991056903519120755197)
                    ·
                      refine ⟨1521746646338819670283199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057991056903519120755197 1521746646338819670283199)
                      ·
                        rfl

theorem cell23_2963591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_2963591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963591 prefixEnd_2963591 := by exact prefixLift 2963591
  have htrace : WordTrace (prefixWord ++ tailWord_2963591) baseStart_2963591 baseEnd_2963591 := by
    simpa [prefixWord, tailWord_2963591, baseEnd_2963591] using wordTrace_append hprefix tailTrace_2963591
  have hstable : (prefixWord ++ tailWord_2963591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963591).length < 2 ^ (prefixWord ++ tailWord_2963591).sum := by decide
  have hdescent : baseEnd_2963591 < baseStart_2963591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963592 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2963592 : Nat := 118140960795 + 2963592 * 2 ^ 59
def prefixEnd_2963592 : Nat := 4983230072969 + 3 ^ 40 * 2963592 * 2
def baseEnd_2963592 : Nat := 1521747159819474166370695

theorem tailTrace_2963592 : CollatzResearch.WordTrace tailWord_2963592 prefixEnd_2963592 1521747159819474166370695 := by
  unfold tailWord_2963592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54045540139709900031374515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72060720186279866708499353 54045540139709900031374515)
  ·
    refine ⟨81068310209564850047061773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54045540139709900031374515 81068310209564850047061773)
    ·
      refine ⟨30400616328586818767648165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81068310209564850047061773 30400616328586818767648165)
      ·
        refine ⟨5700115561610028518934031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30400616328586818767648165 5700115561610028518934031)
        ·
          refine ⟨8550173342415042778401047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700115561610028518934031 8550173342415042778401047)
          ·
            refine ⟨12825260013622564167601571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8550173342415042778401047 12825260013622564167601571)
            ·
              refine ⟨19237890020433846251402357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12825260013622564167601571 19237890020433846251402357)
              ·
                refine ⟨1803552189415673086068971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19237890020433846251402357 1803552189415673086068971)
                ·
                  refine ⟨2705328284123509629103457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803552189415673086068971 2705328284123509629103457)
                  ·
                    refine ⟨2028996213092632221827593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2705328284123509629103457 2028996213092632221827593)
                    ·
                      refine ⟨1521747159819474166370695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028996213092632221827593 1521747159819474166370695)
                      ·
                        rfl

theorem cell23_2963592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2963592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963592 prefixEnd_2963592 := by exact prefixLift 2963592
  have htrace : WordTrace (prefixWord ++ tailWord_2963592) baseStart_2963592 baseEnd_2963592 := by
    simpa [prefixWord, tailWord_2963592, baseEnd_2963592] using wordTrace_append hprefix tailTrace_2963592
  have hstable : (prefixWord ++ tailWord_2963592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963592).length < 2 ^ (prefixWord ++ tailWord_2963592).sum := by decide
  have hdescent : baseEnd_2963592 < baseStart_2963592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963676 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2963676 : Nat := 118140960795 + 2963676 * 2 ^ 59
def prefixEnd_2963676 : Nat := 4983230072969 + 3 ^ 40 * 2963676 * 2
def baseEnd_2963676 : Nat := 1521790292194451837720309

theorem tailTrace_2963676 : CollatzResearch.WordTrace tailWord_2963676 prefixEnd_2963676 1521790292194451837720309 := by
  unfold tailWord_2963676
  simp only [CollatzResearch.WordTrace]
  refine ⟨54047072005557741204403441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72062762674076988272537921 54047072005557741204403441)
  ·
    refine ⟨40535304004168305903302581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54047072005557741204403441 40535304004168305903302581)
    ·
      refine ⟨3800184750390778678434617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40535304004168305903302581 3800184750390778678434617)
      ·
        refine ⟨2850138562793084008825963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3800184750390778678434617 2850138562793084008825963)
        ·
          refine ⟨4275207844189626013238945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850138562793084008825963 4275207844189626013238945)
          ·
            refine ⟨3206405883142219509929209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4275207844189626013238945 3206405883142219509929209)
            ·
              refine ⟨2404804412356664632446907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206405883142219509929209 2404804412356664632446907)
              ·
                refine ⟨3607206618534996948670361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404804412356664632446907 3607206618534996948670361)
                ·
                  refine ⟨2705404963901247711502771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607206618534996948670361 2705404963901247711502771)
                  ·
                    refine ⟨4058107445851871567254157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705404963901247711502771 4058107445851871567254157)
                    ·
                      refine ⟨1521790292194451837720309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4058107445851871567254157 1521790292194451837720309)
                      ·
                        rfl

theorem cell23_2963676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2963676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963676 prefixEnd_2963676 := by exact prefixLift 2963676
  have htrace : WordTrace (prefixWord ++ tailWord_2963676) baseStart_2963676 baseEnd_2963676 := by
    simpa [prefixWord, tailWord_2963676, baseEnd_2963676] using wordTrace_append hprefix tailTrace_2963676
  have hstable : (prefixWord ++ tailWord_2963676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963676).length < 2 ^ (prefixWord ++ tailWord_2963676).sum := by decide
  have hdescent : baseEnd_2963676 < baseStart_2963676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963681 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2963681 : Nat := 118140960795 + 2963681 * 2 ^ 59
def prefixEnd_2963681 : Nat := 4983230072969 + 3 ^ 40 * 2963681 * 2
def baseEnd_2963681 : Nat := 1521792859597724318157785

theorem tailTrace_2963681 : CollatzResearch.WordTrace tailWord_2963681 prefixEnd_2963681 1521792859597724318157785 := by
  unfold tailWord_2963681
  simp only [CollatzResearch.WordTrace]
  refine ⟨108094326376097368262738897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72062884250731578841825931 108094326376097368262738897)
  ·
    refine ⟨81070744782073026197054173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108094326376097368262738897 81070744782073026197054173)
    ·
      refine ⟨30401529293277384823895315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81070744782073026197054173 30401529293277384823895315)
      ·
        refine ⟨45602293939916077235842973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30401529293277384823895315 45602293939916077235842973)
        ·
          refine ⟨17100860227468528963441115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45602293939916077235842973 17100860227468528963441115)
          ·
            refine ⟨25651290341202793445161673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100860227468528963441115 25651290341202793445161673)
            ·
              refine ⟨19238467755902095083871255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25651290341202793445161673 19238467755902095083871255)
              ·
                refine ⟨28857701633853142625806883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19238467755902095083871255 28857701633853142625806883)
                ·
                  refine ⟨43286552450779713938710325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28857701633853142625806883 43286552450779713938710325)
                  ·
                    refine ⟨4058114292260598181754093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43286552450779713938710325 4058114292260598181754093)
                    ·
                      refine ⟨1521792859597724318157785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4058114292260598181754093 1521792859597724318157785)
                      ·
                        rfl

theorem cell23_2963681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2963681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963681 prefixEnd_2963681 := by exact prefixLift 2963681
  have htrace : WordTrace (prefixWord ++ tailWord_2963681) baseStart_2963681 baseEnd_2963681 := by
    simpa [prefixWord, tailWord_2963681, baseEnd_2963681] using wordTrace_append hprefix tailTrace_2963681
  have hstable : (prefixWord ++ tailWord_2963681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963681).length < 2 ^ (prefixWord ++ tailWord_2963681).sum := by decide
  have hdescent : baseEnd_2963681 < baseStart_2963681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963731 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 7, 4]
def baseStart_2963731 : Nat := 118140960795 + 2963731 * 2 ^ 59
def prefixEnd_2963731 : Nat := 4983230072969 + 3 ^ 40 * 2963731 * 2
def baseEnd_2963731 : Nat := 507272844543483040844185

theorem tailTrace_2963731 : CollatzResearch.WordTrace tailWord_2963731 prefixEnd_2963731 507272844543483040844185 := by
  unfold tailWord_2963731
  simp only [CollatzResearch.WordTrace]
  refine ⟨108096150025916226802059047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72064100017277484534706031 108096150025916226802059047)
  ·
    refine ⟨162144225038874340203088571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108096150025916226802059047 162144225038874340203088571)
    ·
      refine ⟨243216337558311510304632857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162144225038874340203088571 243216337558311510304632857)
      ·
        refine ⟨182412253168733632728474643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243216337558311510304632857 182412253168733632728474643)
        ·
          refine ⟨273618379753100449092711965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182412253168733632728474643 273618379753100449092711965)
          ·
            refine ⟨102606892407412668409766987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273618379753100449092711965 102606892407412668409766987)
            ·
              refine ⟨153910338611119002614650481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102606892407412668409766987 153910338611119002614650481)
              ·
                refine ⟨115432753958339251960987861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153910338611119002614650481 115432753958339251960987861)
                ·
                  refine ⟨2705455170898576217835653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 115432753958339251960987861 2705455170898576217835653)
                  ·
                    refine ⟨507272844543483040844185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705455170898576217835653 507272844543483040844185)
                    ·
                      rfl

theorem cell23_2963731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 4].length) (baseStart_2963731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963731 prefixEnd_2963731 := by exact prefixLift 2963731
  have htrace : WordTrace (prefixWord ++ tailWord_2963731) baseStart_2963731 baseEnd_2963731 := by
    simpa [prefixWord, tailWord_2963731, baseEnd_2963731] using wordTrace_append hprefix tailTrace_2963731
  have hstable : (prefixWord ++ tailWord_2963731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963731).length < 2 ^ (prefixWord ++ tailWord_2963731).sum := by decide
  have hdescent : baseEnd_2963731 < baseStart_2963731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963748 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_2963748 : Nat := 118140960795 + 2963748 * 2 ^ 59
def prefixEnd_2963748 : Nat := 4983230072969 + 3 ^ 40 * 2963748 * 2
def baseEnd_2963748 : Nat := 507275754267191852006659

theorem tailTrace_2963748 : CollatzResearch.WordTrace tailWord_2963748 prefixEnd_2963748 507275754267191852006659 := by
  unfold tailWord_2963748
  simp only [CollatzResearch.WordTrace]
  refine ⟨54048385033427319352713949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72064513377903092470285265 54048385033427319352713949)
  ·
    refine ⟨20268144387535244757267731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54048385033427319352713949 20268144387535244757267731)
    ·
      refine ⟨30402216581302867135901597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20268144387535244757267731 30402216581302867135901597)
      ·
        refine ⟨11400831217988575175963099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30402216581302867135901597 11400831217988575175963099)
        ·
          refine ⟨17101246826982862763944649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400831217988575175963099 17101246826982862763944649)
          ·
            refine ⟨12825935120237147072958487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17101246826982862763944649 12825935120237147072958487)
            ·
              refine ⟨19238902680355720609437731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12825935120237147072958487 19238902680355720609437731)
              ·
                refine ⟨28858354020533580914156597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19238902680355720609437731 28858354020533580914156597)
                ·
                  refine ⟨2705470689425023210702181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28858354020533580914156597 2705470689425023210702181)
                  ·
                    refine ⟨507275754267191852006659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705470689425023210702181 507275754267191852006659)
                    ·
                      rfl

theorem cell23_2963748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_2963748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963748 prefixEnd_2963748 := by exact prefixLift 2963748
  have htrace : WordTrace (prefixWord ++ tailWord_2963748) baseStart_2963748 baseEnd_2963748 := by
    simpa [prefixWord, tailWord_2963748, baseEnd_2963748] using wordTrace_append hprefix tailTrace_2963748
  have hstable : (prefixWord ++ tailWord_2963748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963748).length < 2 ^ (prefixWord ++ tailWord_2963748).sum := by decide
  have hdescent : baseEnd_2963748 < baseStart_2963748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963752 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2963752 : Nat := 118140960795 + 2963752 * 2 ^ 59
def prefixEnd_2963752 : Nat := 4983230072969 + 3 ^ 40 * 2963752 * 2
def baseEnd_2963752 : Nat := 507276438908064513456653

theorem tailTrace_2963752 : CollatzResearch.WordTrace tailWord_2963752 prefixEnd_2963752 507276438908064513456653 := by
  unfold tailWord_2963752
  simp only [CollatzResearch.WordTrace]
  refine ⟨54048457979420073694286755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72064610639226764925715673 54048457979420073694286755)
  ·
    refine ⟨81072686969130110541430133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54048457979420073694286755 81072686969130110541430133)
    ·
      refine ⟨7600564403355947863259075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81072686969130110541430133 7600564403355947863259075)
      ·
        refine ⟨11400846605033921794888613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7600564403355947863259075 11400846605033921794888613)
        ·
          refine ⟨2137658738443860336541615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11400846605033921794888613 2137658738443860336541615)
          ·
            refine ⟨3206488107665790504812423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137658738443860336541615 3206488107665790504812423)
            ·
              refine ⟨4809732161498685757218635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206488107665790504812423 4809732161498685757218635)
              ·
                refine ⟨7214598242248028635827953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4809732161498685757218635 7214598242248028635827953)
                ·
                  refine ⟨5410948681686021476870965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7214598242248028635827953 5410948681686021476870965)
                  ·
                    refine ⟨507276438908064513456653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5410948681686021476870965 507276438908064513456653)
                    ·
                      rfl

theorem cell23_2963752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2963752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963752 prefixEnd_2963752 := by exact prefixLift 2963752
  have htrace : WordTrace (prefixWord ++ tailWord_2963752) baseStart_2963752 baseEnd_2963752 := by
    simpa [prefixWord, tailWord_2963752, baseEnd_2963752] using wordTrace_append hprefix tailTrace_2963752
  have hstable : (prefixWord ++ tailWord_2963752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963752).length < 2 ^ (prefixWord ++ tailWord_2963752).sum := by decide
  have hdescent : baseEnd_2963752 < baseStart_2963752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963791 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 3, 5]
def baseStart_2963791 : Nat := 118140960795 + 2963791 * 2 ^ 59
def prefixEnd_2963791 : Nat := 4983230072969 + 3 ^ 40 * 2963791 * 2
def baseEnd_2963791 : Nat := 507283114156572962594093

theorem tailTrace_2963791 : CollatzResearch.WordTrace tailWord_2963791 prefixEnd_2963791 507283114156572962594093 := by
  unfold tailWord_2963791
  simp only [CollatzResearch.WordTrace]
  refine ⟨108098338405698857049243227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72065558937132571366162151 108098338405698857049243227)
  ·
    refine ⟨162147507608548285573864841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108098338405698857049243227 162147507608548285573864841)
    ·
      refine ⟨121610630706411214180398631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162147507608548285573864841 121610630706411214180398631)
      ·
        refine ⟨182415946059616821270597947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121610630706411214180398631 182415946059616821270597947)
        ·
          refine ⟨273623919089425231905896921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182415946059616821270597947 273623919089425231905896921)
          ·
            refine ⟨205217939317068923929422691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273623919089425231905896921 205217939317068923929422691)
            ·
              refine ⟨307826908975603385894134037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205217939317068923929422691 307826908975603385894134037)
              ·
                refine ⟨14429386358231408713787533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307826908975603385894134037 14429386358231408713787533)
                ·
                  refine ⟨5411019884336778267670325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14429386358231408713787533 5411019884336778267670325)
                  ·
                    refine ⟨507283114156572962594093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5411019884336778267670325 507283114156572962594093)
                    ·
                      rfl

theorem cell23_2963791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_2963791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963791 prefixEnd_2963791 := by exact prefixLift 2963791
  have htrace : WordTrace (prefixWord ++ tailWord_2963791) baseStart_2963791 baseEnd_2963791 := by
    simpa [prefixWord, tailWord_2963791, baseEnd_2963791] using wordTrace_append hprefix tailTrace_2963791
  have hstable : (prefixWord ++ tailWord_2963791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963791).length < 2 ^ (prefixWord ++ tailWord_2963791).sum := by decide
  have hdescent : baseEnd_2963791 < baseStart_2963791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963815 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_2963815 : Nat := 118140960795 + 2963815 * 2 ^ 59
def prefixEnd_2963815 : Nat := 4983230072969 + 3 ^ 40 * 2963815 * 2
def baseEnd_2963815 : Nat := 1521861666005426793882169

theorem tailTrace_2963815 : CollatzResearch.WordTrace tailWord_2963815 prefixEnd_2963815 1521861666005426793882169 := by
  unfold tailWord_2963815
  simp only [CollatzResearch.WordTrace]
  refine ⟨108099213757611909148116899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72066142505074606098744599 108099213757611909148116899)
  ·
    refine ⟨162148820636417863722175349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108099213757611909148116899 162148820636417863722175349)
    ·
      refine ⟨15201451934664174723953939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162148820636417863722175349 15201451934664174723953939)
      ·
        refine ⟨22802177901996262085930909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15201451934664174723953939 22802177901996262085930909)
        ·
          refine ⟨8550816713248598282224091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22802177901996262085930909 8550816713248598282224091)
          ·
            refine ⟨12826225069872897423336137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8550816713248598282224091 12826225069872897423336137)
            ·
              refine ⟨9619668802404673067502103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12826225069872897423336137 9619668802404673067502103)
              ·
                refine ⟨14429503203607009601253155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9619668802404673067502103 14429503203607009601253155)
                ·
                  refine ⟨21644254805410514401879733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14429503203607009601253155 21644254805410514401879733)
                  ·
                    refine ⟨2029148888007235725176225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21644254805410514401879733 2029148888007235725176225)
                    ·
                      refine ⟨1521861666005426793882169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029148888007235725176225 1521861666005426793882169)
                      ·
                        rfl

theorem cell23_2963815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_2963815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963815 prefixEnd_2963815 := by exact prefixLift 2963815
  have htrace : WordTrace (prefixWord ++ tailWord_2963815) baseStart_2963815 baseEnd_2963815 := by
    simpa [prefixWord, tailWord_2963815, baseEnd_2963815] using wordTrace_append hprefix tailTrace_2963815
  have hstable : (prefixWord ++ tailWord_2963815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963815).length < 2 ^ (prefixWord ++ tailWord_2963815).sum := by decide
  have hdescent : baseEnd_2963815 < baseStart_2963815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963848 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2963848 : Nat := 118140960795 + 2963848 * 2 ^ 59
def prefixEnd_2963848 : Nat := 4983230072969 + 3 ^ 40 * 2963848 * 2
def baseEnd_2963848 : Nat := 1521878610867025164769517

theorem tailTrace_2963848 : CollatzResearch.WordTrace tailWord_2963848 prefixEnd_2963848 1521878610867025164769517 := by
  unfold tailWord_2963848
  simp only [CollatzResearch.WordTrace]
  refine ⟨54050208683246177892034099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72066944910994903856045465 54050208683246177892034099)
  ·
    refine ⟨81075313024869266838051149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54050208683246177892034099 81075313024869266838051149)
    ·
      refine ⟨30403242384325975064269181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81075313024869266838051149 30403242384325975064269181)
      ·
        refine ⟨11401215894122240649100943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30403242384325975064269181 11401215894122240649100943)
        ·
          refine ⟨17101823841183360973651415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11401215894122240649100943 17101823841183360973651415)
          ·
            refine ⟨25652735761775041460477123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17101823841183360973651415 25652735761775041460477123)
            ·
              refine ⟨38479103642662562190715685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25652735761775041460477123 38479103642662562190715685)
              ·
                refine ⟨7214831932999230410759191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38479103642662562190715685 7214831932999230410759191)
                ·
                  refine ⟨10822247899498845616138787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214831932999230410759191 10822247899498845616138787)
                  ·
                    refine ⟨16233371849248268424208181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10822247899498845616138787 16233371849248268424208181)
                    ·
                      refine ⟨1521878610867025164769517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16233371849248268424208181 1521878610867025164769517)
                      ·
                        rfl

theorem cell23_2963848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2963848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963848 prefixEnd_2963848 := by exact prefixLift 2963848
  have htrace : WordTrace (prefixWord ++ tailWord_2963848) baseStart_2963848 baseEnd_2963848 := by
    simpa [prefixWord, tailWord_2963848, baseEnd_2963848] using wordTrace_append hprefix tailTrace_2963848
  have hstable : (prefixWord ++ tailWord_2963848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963848).length < 2 ^ (prefixWord ++ tailWord_2963848).sum := by decide
  have hdescent : baseEnd_2963848 < baseStart_2963848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963851 : List Nat := [1, 1, 1, 1, 4, 4, 1, 10]
def baseStart_2963851 : Nat := 118140960795 + 2963851 * 2 ^ 59
def prefixEnd_2963851 : Nat := 4983230072969 + 3 ^ 40 * 2963851 * 2
def baseEnd_2963851 : Nat := 56365931529962542704889

theorem tailTrace_2963851 : CollatzResearch.WordTrace tailWord_2963851 prefixEnd_2963851 56365931529962542704889 := by
  unfold tailWord_2963851
  simp only [CollatzResearch.WordTrace]
  refine ⟨108100526785481487296427407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72067017856987658197618271 108100526785481487296427407)
  ·
    refine ⟨162150790178222230944641111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108100526785481487296427407 162150790178222230944641111)
    ·
      refine ⟨243226185267333346416961667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162150790178222230944641111 243226185267333346416961667)
      ·
        refine ⟨364839277901000019625442501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243226185267333346416961667 364839277901000019625442501)
        ·
          refine ⟨68407364606437503679770469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364839277901000019625442501 68407364606437503679770469)
          ·
            refine ⟨12826380863707031939956963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68407364606437503679770469 12826380863707031939956963)
            ·
              refine ⟨19239571295560547909935445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12826380863707031939956963 19239571295560547909935445)
              ·
                refine ⟨56365931529962542704889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19239571295560547909935445 56365931529962542704889)
                ·
                  rfl

theorem cell23_2963851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 10].length) (baseStart_2963851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963851 prefixEnd_2963851 := by exact prefixLift 2963851
  have htrace : WordTrace (prefixWord ++ tailWord_2963851) baseStart_2963851 baseEnd_2963851 := by
    simpa [prefixWord, tailWord_2963851, baseEnd_2963851] using wordTrace_append hprefix tailTrace_2963851
  have hstable : (prefixWord ++ tailWord_2963851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963851).length < 2 ^ (prefixWord ++ tailWord_2963851).sum := by decide
  have hdescent : baseEnd_2963851 < baseStart_2963851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963881 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_2963881 : Nat := 118140960795 + 2963881 * 2 ^ 59
def prefixEnd_2963881 : Nat := 4983230072969 + 3 ^ 40 * 2963881 * 2
def baseEnd_2963881 : Nat := 507298518576207845218955

theorem tailTrace_2963881 : CollatzResearch.WordTrace tailWord_2963881 prefixEnd_2963881 507298518576207845218955 := by
  unfold tailWord_2963881
  simp only [CollatzResearch.WordTrace]
  refine ⟨108101620975372802420019497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72067747316915201613346331 108101620975372802420019497)
  ·
    refine ⟨81076215731529601815014623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108101620975372802420019497 81076215731529601815014623)
    ·
      refine ⟨121614323597294402722521935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81076215731529601815014623 121614323597294402722521935)
      ·
        refine ⟨182421485395941604083782903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121614323597294402722521935 182421485395941604083782903)
        ·
          refine ⟨273632228093912406125674355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182421485395941604083782903 273632228093912406125674355)
          ·
            refine ⟨410448342140868609188511533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273632228093912406125674355 410448342140868609188511533)
            ·
              refine ⟨153918128302825728445691825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410448342140868609188511533 153918128302825728445691825)
              ·
                refine ⟨115438596227119296334268869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153918128302825728445691825 115438596227119296334268869)
                ·
                  refine ⟨21644736792584868062675413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115438596227119296334268869 21644736792584868062675413)
                  ·
                    refine ⟨507298518576207845218955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21644736792584868062675413 507298518576207845218955)
                    ·
                      rfl

theorem cell23_2963881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_2963881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963881 prefixEnd_2963881 := by exact prefixLift 2963881
  have htrace : WordTrace (prefixWord ++ tailWord_2963881) baseStart_2963881 baseEnd_2963881 := by
    simpa [prefixWord, tailWord_2963881, baseEnd_2963881] using wordTrace_append hprefix tailTrace_2963881
  have hstable : (prefixWord ++ tailWord_2963881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963881).length < 2 ^ (prefixWord ++ tailWord_2963881).sum := by decide
  have hdescent : baseEnd_2963881 < baseStart_2963881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963885 : List Nat := [1, 5, 2, 2, 3, 10]
def baseStart_2963885 : Nat := 118140960795 + 2963885 * 2 ^ 59
def prefixEnd_2963885 : Nat := 4983230072969 + 3 ^ 40 * 2963885 * 2
def baseEnd_2963885 : Nat := 6262953126136796378629

theorem tailTrace_2963885 : CollatzResearch.WordTrace tailWord_2963885 prefixEnd_2963885 6262953126136796378629 := by
  unfold tailWord_2963885
  simp only [CollatzResearch.WordTrace]
  refine ⟨108101766867358311103165109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72067844578238874068776739 108101766867358311103165109)
  ·
    refine ⟨10134540643814841665921729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108101766867358311103165109 10134540643814841665921729)
    ·
      refine ⟨7600905482861131249441297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10134540643814841665921729 7600905482861131249441297)
      ·
        refine ⟨5700679112145848437080973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7600905482861131249441297 5700679112145848437080973)
        ·
          refine ⟨2137754667054693163905365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5700679112145848437080973 2137754667054693163905365)
          ·
            refine ⟨6262953126136796378629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2137754667054693163905365 6262953126136796378629)
            ·
              rfl

theorem cell23_2963885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 10].length) (baseStart_2963885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963885 prefixEnd_2963885 := by exact prefixLift 2963885
  have htrace : WordTrace (prefixWord ++ tailWord_2963885) baseStart_2963885 baseEnd_2963885 := by
    simpa [prefixWord, tailWord_2963885, baseEnd_2963885] using wordTrace_append hprefix tailTrace_2963885
  have hstable : (prefixWord ++ tailWord_2963885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963885).length < 2 ^ (prefixWord ++ tailWord_2963885).sum := by decide
  have hdescent : baseEnd_2963885 < baseStart_2963885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963891 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_2963891 : Nat := 118140960795 + 2963891 * 2 ^ 59
def prefixEnd_2963891 : Nat := 4983230072969 + 3 ^ 40 * 2963891 * 2
def baseEnd_2963891 : Nat := 1521900690535168496531819

theorem tailTrace_2963891 : CollatzResearch.WordTrace tailWord_2963891 prefixEnd_2963891 1521900690535168496531819 := by
  unfold tailWord_2963891
  simp only [CollatzResearch.WordTrace]
  refine ⟨108101985705336574127883527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72067990470224382751922351 108101985705336574127883527)
  ·
    refine ⟨162152978558004861191825291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108101985705336574127883527 162152978558004861191825291)
    ·
      refine ⟨243229467837007291787737937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162152978558004861191825291 243229467837007291787737937)
      ·
        refine ⟨182422100877755468840803453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243229467837007291787737937 182422100877755468840803453)
        ·
          refine ⟨68408287829158300815301295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182422100877755468840803453 68408287829158300815301295)
          ·
            refine ⟨102612431743737451222951943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68408287829158300815301295 102612431743737451222951943)
            ·
              refine ⟨153918647615606176834427915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102612431743737451222951943 153918647615606176834427915)
              ·
                refine ⟨230877971423409265251641873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153918647615606176834427915 230877971423409265251641873)
                ·
                  refine ⟨173158478567556948938731405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230877971423409265251641873 173158478567556948938731405)
                  ·
                    refine ⟨64934429462833855852024277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173158478567556948938731405 64934429462833855852024277)
                    ·
                      refine ⟨1521900690535168496531819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64934429462833855852024277 1521900690535168496531819)
                      ·
                        rfl

theorem cell23_2963891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_2963891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963891 prefixEnd_2963891 := by exact prefixLift 2963891
  have htrace : WordTrace (prefixWord ++ tailWord_2963891) baseStart_2963891 baseEnd_2963891 := by
    simpa [prefixWord, tailWord_2963891, baseEnd_2963891] using wordTrace_append hprefix tailTrace_2963891
  have hstable : (prefixWord ++ tailWord_2963891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963891).length < 2 ^ (prefixWord ++ tailWord_2963891).sum := by decide
  have hdescent : baseEnd_2963891 < baseStart_2963891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963912 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_2963912 : Nat := 118140960795 + 2963912 * 2 ^ 59
def prefixEnd_2963912 : Nat := 4983230072969 + 3 ^ 40 * 2963912 * 2
def baseEnd_2963912 : Nat := 1521911473628912914369223

theorem tailTrace_2963912 : CollatzResearch.WordTrace tailWord_2963912 prefixEnd_2963912 1521911473628912914369223 := by
  unfold tailWord_2963912
  simp only [CollatzResearch.WordTrace]
  refine ⟨54051375819130247357198995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72068501092173663142931993 54051375819130247357198995)
  ·
    refine ⟨81077063728695371035798493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54051375819130247357198995 81077063728695371035798493)
    ·
      refine ⟨30403898898260764138424435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81077063728695371035798493 30403898898260764138424435)
      ·
        refine ⟨45605848347391146207636653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30403898898260764138424435 45605848347391146207636653)
        ·
          refine ⟨17102193130271679827863745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45605848347391146207636653 17102193130271679827863745)
          ·
            refine ⟨12826644847703759870897809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17102193130271679827863745 12826644847703759870897809)
            ·
              refine ⟨9619983635777819903173357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12826644847703759870897809 9619983635777819903173357)
              ·
                refine ⟨3607493863416682463690009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9619983635777819903173357 3607493863416682463690009)
                ·
                  refine ⟨2705620397562511847767507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607493863416682463690009 2705620397562511847767507)
                  ·
                    refine ⟨4058430596343767771651261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705620397562511847767507 4058430596343767771651261)
                    ·
                      refine ⟨1521911473628912914369223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4058430596343767771651261 1521911473628912914369223)
                      ·
                        rfl

theorem cell23_2963912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_2963912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963912 prefixEnd_2963912 := by exact prefixLift 2963912
  have htrace : WordTrace (prefixWord ++ tailWord_2963912) baseStart_2963912 baseEnd_2963912 := by
    simpa [prefixWord, tailWord_2963912, baseEnd_2963912] using wordTrace_append hprefix tailTrace_2963912
  have hstable : (prefixWord ++ tailWord_2963912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963912).length < 2 ^ (prefixWord ++ tailWord_2963912).sum := by decide
  have hdescent : baseEnd_2963912 < baseStart_2963912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963918 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2963918 : Nat := 118140960795 + 2963918 * 2 ^ 59
def prefixEnd_2963918 : Nat := 4983230072969 + 3 ^ 40 * 2963918 * 2
def baseEnd_2963918 : Nat := 1521914554512839890894195

theorem tailTrace_2963918 : CollatzResearch.WordTrace tailWord_2963918 prefixEnd_2963918 1521914554512839890894195 := by
  unfold tailWord_2963918
  simp only [CollatzResearch.WordTrace]
  refine ⟨13512871309529844717389551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72068646984159171826077605 13512871309529844717389551)
  ·
    refine ⟨20269306964294767076084327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13512871309529844717389551 20269306964294767076084327)
    ·
      refine ⟨30403960446442150614126491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20269306964294767076084327 30403960446442150614126491)
      ·
        refine ⟨45605940669663225921189737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30403960446442150614126491 45605940669663225921189737)
        ·
          refine ⟨34204455502247419440892303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45605940669663225921189737 34204455502247419440892303)
          ·
            refine ⟨51306683253371129161338455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34204455502247419440892303 51306683253371129161338455)
            ·
              refine ⟨76960024880056693742007683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51306683253371129161338455 76960024880056693742007683)
              ·
                refine ⟨115440037320085040613011525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76960024880056693742007683 115440037320085040613011525)
                ·
                  refine ⟨21645006997515945114939661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115440037320085040613011525 21645006997515945114939661)
                  ·
                    refine ⟨8116877624068479418102373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21645006997515945114939661 8116877624068479418102373)
                    ·
                      refine ⟨1521914554512839890894195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8116877624068479418102373 1521914554512839890894195)
                      ·
                        rfl

theorem cell23_2963918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2963918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963918 prefixEnd_2963918 := by exact prefixLift 2963918
  have htrace : WordTrace (prefixWord ++ tailWord_2963918) baseStart_2963918 baseEnd_2963918 := by
    simpa [prefixWord, tailWord_2963918, baseEnd_2963918] using wordTrace_append hprefix tailTrace_2963918
  have hstable : (prefixWord ++ tailWord_2963918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963918).length < 2 ^ (prefixWord ++ tailWord_2963918).sum := by decide
  have hdescent : baseEnd_2963918 < baseStart_2963918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963939 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2963939 : Nat := 118140960795 + 2963939 * 2 ^ 59
def prefixEnd_2963939 : Nat := 4983230072969 + 3 ^ 40 * 2963939 * 2
def baseEnd_2963939 : Nat := 1521925337606584308731599

theorem tailTrace_2963939 : CollatzResearch.WordTrace tailWord_2963939 prefixEnd_2963939 1521925337606584308731599 := by
  unfold tailWord_2963939
  simp only [CollatzResearch.WordTrace]
  refine ⟨108103736409162678325630871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72069157606108452217087247 108103736409162678325630871)
  ·
    refine ⟨162155604613744017488446307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108103736409162678325630871 162155604613744017488446307)
    ·
      refine ⟨243233406920616026232669461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162155604613744017488446307 243233406920616026232669461)
      ·
        refine ⟨11401565949403876229656381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243233406920616026232669461 11401565949403876229656381)
        ·
          refine ⟨4275587231026453586121143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11401565949403876229656381 4275587231026453586121143)
          ·
            refine ⟨6413380846539680379181715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275587231026453586121143 6413380846539680379181715)
            ·
              refine ⟨9620071269809520568772573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413380846539680379181715 9620071269809520568772573)
              ·
                refine ⟨3607526726178570213289715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9620071269809520568772573 3607526726178570213289715)
                ·
                  refine ⟨5411290089267855319934573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607526726178570213289715 5411290089267855319934573)
                  ·
                    refine ⟨2029233783475445744975465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5411290089267855319934573 2029233783475445744975465)
                    ·
                      refine ⟨1521925337606584308731599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029233783475445744975465 1521925337606584308731599)
                      ·
                        rfl

theorem cell23_2963939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2963939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963939 prefixEnd_2963939 := by exact prefixLift 2963939
  have htrace : WordTrace (prefixWord ++ tailWord_2963939) baseStart_2963939 baseEnd_2963939 := by
    simpa [prefixWord, tailWord_2963939, baseEnd_2963939] using wordTrace_append hprefix tailTrace_2963939
  have hstable : (prefixWord ++ tailWord_2963939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963939).length < 2 ^ (prefixWord ++ tailWord_2963939).sum := by decide
  have hdescent : baseEnd_2963939 < baseStart_2963939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963948 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_2963948 : Nat := 118140960795 + 2963948 * 2 ^ 59
def prefixEnd_2963948 : Nat := 4983230072969 + 3 ^ 40 * 2963948 * 2
def baseEnd_2963948 : Nat := 1521929958932474773519057

theorem tailTrace_2963948 : CollatzResearch.WordTrace tailWord_2963948 prefixEnd_2963948 1521929958932474773519057 := by
  unfold tailWord_2963948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54052032333065036431354249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72069376444086715241805665 54052032333065036431354249)
  ·
    refine ⟨40539024249798777323515687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54052032333065036431354249 40539024249798777323515687)
    ·
      refine ⟨60808536374698165985273531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40539024249798777323515687 60808536374698165985273531)
      ·
        refine ⟨91212804562047248977910297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60808536374698165985273531 91212804562047248977910297)
        ·
          refine ⟨68409603421535436733432723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91212804562047248977910297 68409603421535436733432723)
          ·
            refine ⟨102614405132303155100149085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68409603421535436733432723 102614405132303155100149085)
            ·
              refine ⟨38480401924613683162555907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102614405132303155100149085 38480401924613683162555907)
              ·
                refine ⟨57720602886920524743833861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38480401924613683162555907 57720602886920524743833861)
                ·
                  refine ⟨10822613041297598389468849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57720602886920524743833861 10822613041297598389468849)
                  ·
                    refine ⟨8116959780973198792101637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10822613041297598389468849 8116959780973198792101637)
                    ·
                      refine ⟨1521929958932474773519057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8116959780973198792101637 1521929958932474773519057)
                      ·
                        rfl

theorem cell23_2963948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_2963948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963948 prefixEnd_2963948 := by exact prefixLift 2963948
  have htrace : WordTrace (prefixWord ++ tailWord_2963948) baseStart_2963948 baseEnd_2963948 := by
    simpa [prefixWord, tailWord_2963948, baseEnd_2963948] using wordTrace_append hprefix tailTrace_2963948
  have hstable : (prefixWord ++ tailWord_2963948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963948).length < 2 ^ (prefixWord ++ tailWord_2963948).sum := by decide
  have hdescent : baseEnd_2963948 < baseStart_2963948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963952 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 4, 2, 2]
def baseStart_2963952 : Nat := 118140960795 + 2963952 * 2 ^ 59
def prefixEnd_2963952 : Nat := 4983230072969 + 3 ^ 40 * 2963952 * 2
def baseEnd_2963952 : Nat := 1521932012855092757869039

theorem tailTrace_2963952 : CollatzResearch.WordTrace tailWord_2963952 prefixEnd_2963952 1521932012855092757869039 := by
  unfold tailWord_2963952
  simp only [CollatzResearch.WordTrace]
  refine ⟨54052105279057790772927055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72069473705410387697236073 54052105279057790772927055)
  ·
    refine ⟨81078157918586686159390583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54052105279057790772927055 81078157918586686159390583)
    ·
      refine ⟨121617236877880029239085875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81078157918586686159390583 121617236877880029239085875)
      ·
        refine ⟨182425855316820043858628813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121617236877880029239085875 182425855316820043858628813)
        ·
          refine ⟨68409695743807516446985805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182425855316820043858628813 68409695743807516446985805)
          ·
            refine ⟨25653635903927818667619677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68409695743807516446985805 25653635903927818667619677)
            ·
              refine ⟨9620113463972932000357379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25653635903927818667619677 9620113463972932000357379)
              ·
                refine ⟨14430170195959398000536069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620113463972932000357379 14430170195959398000536069)
                ·
                  refine ⟨2705656911742387125100513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14430170195959398000536069 2705656911742387125100513)
                  ·
                    refine ⟨2029242683806790343825385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2705656911742387125100513 2029242683806790343825385)
                    ·
                      refine ⟨1521932012855092757869039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029242683806790343825385 1521932012855092757869039)
                      ·
                        rfl

theorem cell23_2963952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 2, 2].length) (baseStart_2963952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963952 prefixEnd_2963952 := by exact prefixLift 2963952
  have htrace : WordTrace (prefixWord ++ tailWord_2963952) baseStart_2963952 baseEnd_2963952 := by
    simpa [prefixWord, tailWord_2963952, baseEnd_2963952] using wordTrace_append hprefix tailTrace_2963952
  have hstable : (prefixWord ++ tailWord_2963952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963952).length < 2 ^ (prefixWord ++ tailWord_2963952).sum := by decide
  have hdescent : baseEnd_2963952 < baseStart_2963952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963969 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_2963969 : Nat := 118140960795 + 2963969 * 2 ^ 59
def prefixEnd_2963969 : Nat := 4983230072969 + 3 ^ 40 * 2963969 * 2
def baseEnd_2963969 : Nat := 1521940742026219191356461

theorem tailTrace_2963969 : CollatzResearch.WordTrace tailWord_2963969 prefixEnd_2963969 1521940742026219191356461 := by
  unfold tailWord_2963969
  simp only [CollatzResearch.WordTrace]
  refine ⟨108104830599053993449222961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72069887066035995632815307 108104830599053993449222961)
  ·
    refine ⟨81078622949290495086917221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108104830599053993449222961 81078622949290495086917221)
    ·
      refine ⟨15202241802991967828796979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81078622949290495086917221 15202241802991967828796979)
      ·
        refine ⟨22803362704487951743195469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15202241802991967828796979 22803362704487951743195469)
        ·
          refine ⟨8551261014182981903698301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22803362704487951743195469 8551261014182981903698301)
          ·
            refine ⟨3206722880318618213886863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8551261014182981903698301 3206722880318618213886863)
            ·
              refine ⟨4810084320477927320830295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206722880318618213886863 4810084320477927320830295)
              ·
                refine ⟨7215126480716890981245443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810084320477927320830295 7215126480716890981245443)
                ·
                  refine ⟨10822689721075336471868165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7215126480716890981245443 10822689721075336471868165)
                  ·
                    refine ⟨2029254322701625588475281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10822689721075336471868165 2029254322701625588475281)
                    ·
                      refine ⟨1521940742026219191356461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029254322701625588475281 1521940742026219191356461)
                      ·
                        rfl

theorem cell23_2963969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_2963969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963969 prefixEnd_2963969 := by exact prefixLift 2963969
  have htrace : WordTrace (prefixWord ++ tailWord_2963969) baseStart_2963969 baseEnd_2963969 := by
    simpa [prefixWord, tailWord_2963969, baseEnd_2963969] using wordTrace_append hprefix tailTrace_2963969
  have hstable : (prefixWord ++ tailWord_2963969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963969).length < 2 ^ (prefixWord ++ tailWord_2963969).sum := by decide
  have hdescent : baseEnd_2963969 < baseStart_2963969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963992 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 5]
def baseStart_2963992 : Nat := 118140960795 + 2963992 * 2 ^ 59
def prefixEnd_2963992 : Nat := 4983230072969 + 3 ^ 40 * 2963992 * 2
def baseEnd_2963992 : Nat := 169105839120141400152095

theorem tailTrace_2963992 : CollatzResearch.WordTrace tailWord_2963992 prefixEnd_2963992 169105839120141400152095 := by
  unfold tailWord_2963992
  simp only [CollatzResearch.WordTrace]
  refine ⟨54052834738985334188655115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72070446318647112251540153 54052834738985334188655115)
  ·
    refine ⟨81079252108478001282982673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54052834738985334188655115 81079252108478001282982673)
    ·
      refine ⟨60809439081358500962237005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81079252108478001282982673 60809439081358500962237005)
      ·
        refine ⟨22803539655509437860838877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60809439081358500962237005 22803539655509437860838877)
        ·
          refine ⟨8551327370816039197814579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22803539655509437860838877 8551327370816039197814579)
          ·
            refine ⟨12826991056224058796721869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551327370816039197814579 12826991056224058796721869)
            ·
              refine ⟨4810121646084022048770701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12826991056224058796721869 4810121646084022048770701)
              ·
                refine ⟨1803795617281508268289013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4810121646084022048770701 1803795617281508268289013)
                ·
                  refine ⟨169105839120141400152095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1803795617281508268289013 169105839120141400152095)
                  ·
                    rfl

theorem cell23_2963992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 5].length) (baseStart_2963992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963992 prefixEnd_2963992 := by exact prefixLift 2963992
  have htrace : WordTrace (prefixWord ++ tailWord_2963992) baseStart_2963992 baseEnd_2963992 := by
    simpa [prefixWord, tailWord_2963992, baseEnd_2963992] using wordTrace_append hprefix tailTrace_2963992
  have hstable : (prefixWord ++ tailWord_2963992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963992).length < 2 ^ (prefixWord ++ tailWord_2963992).sum := by decide
  have hdescent : baseEnd_2963992 < baseStart_2963992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964025 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2964025 : Nat := 118140960795 + 2964025 * 2 ^ 59
def prefixEnd_2964025 : Nat := 4983230072969 + 3 ^ 40 * 2964025 * 2
def baseEnd_2964025 : Nat := 1521969496942870972256203

theorem tailTrace_2964025 : CollatzResearch.WordTrace tailWord_2964025 prefixEnd_2964025 1521969496942870972256203 := by
  unfold tailWord_2964025
  simp only [CollatzResearch.WordTrace]
  refine ⟨108106873086851115013261529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72071248724567410008841019 108106873086851115013261529)
  ·
    refine ⟨81080154815138336259946147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108106873086851115013261529 81080154815138336259946147)
    ·
      refine ⟨121620232222707504389919221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81080154815138336259946147 121620232222707504389919221)
      ·
        refine ⟨11401896770878828536554927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121620232222707504389919221 11401896770878828536554927)
        ·
          refine ⟨17102845156318242804832391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11401896770878828536554927 17102845156318242804832391)
          ·
            refine ⟨25654267734477364207248587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17102845156318242804832391 25654267734477364207248587)
            ·
              refine ⟨38481401601716046310872881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25654267734477364207248587 38481401601716046310872881)
              ·
                refine ⟨28861051201287034733154661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38481401601716046310872881 28861051201287034733154661)
                ·
                  refine ⟨5411447100241319012466499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28861051201287034733154661 5411447100241319012466499)
                  ·
                    refine ⟨8117170650361978518699749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5411447100241319012466499 8117170650361978518699749)
                    ·
                      refine ⟨1521969496942870972256203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8117170650361978518699749 1521969496942870972256203)
                      ·
                        rfl

theorem cell23_2964025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2964025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964025 prefixEnd_2964025 := by exact prefixLift 2964025
  have htrace : WordTrace (prefixWord ++ tailWord_2964025) baseStart_2964025 baseEnd_2964025 := by
    simpa [prefixWord, tailWord_2964025, baseEnd_2964025] using wordTrace_append hprefix tailTrace_2964025
  have hstable : (prefixWord ++ tailWord_2964025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964025).length < 2 ^ (prefixWord ++ tailWord_2964025).sum := by decide
  have hdescent : baseEnd_2964025 < baseStart_2964025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964035 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 3, 4]
def baseStart_2964035 : Nat := 118140960795 + 2964035 * 2 ^ 59
def prefixEnd_2964035 : Nat := 4983230072969 + 3 ^ 40 * 2964035 * 2
def baseEnd_2964035 : Nat := 507324877249805311043719

theorem tailTrace_2964035 : CollatzResearch.WordTrace tailWord_2964035 prefixEnd_2964035 507324877249805311043719 := by
  unfold tailWord_2964035
  simp only [CollatzResearch.WordTrace]
  refine ⟨108107237816814886721125559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72071491877876591147417039 108107237816814886721125559)
  ·
    refine ⟨162160856725222330081688339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108107237816814886721125559 162160856725222330081688339)
    ·
      refine ⟨243241285087833495122532509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162160856725222330081688339 243241285087833495122532509)
      ·
        refine ⟨91215481907937560670949691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243241285087833495122532509 91215481907937560670949691)
        ·
          refine ⟨136823222861906341006424537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91215481907937560670949691 136823222861906341006424537)
          ·
            refine ⟨102617417146429755754818403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136823222861906341006424537 102617417146429755754818403)
            ·
              refine ⟨153926125719644633632227605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102617417146429755754818403 153926125719644633632227605)
              ·
                refine ⟨7215287143108342201510669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153926125719644633632227605 7215287143108342201510669)
                ·
                  refine ⟨2705732678665628325566501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7215287143108342201510669 2705732678665628325566501)
                  ·
                    refine ⟨507324877249805311043719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705732678665628325566501 507324877249805311043719)
                    ·
                      rfl

theorem cell23_2964035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 4].length) (baseStart_2964035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964035 prefixEnd_2964035 := by exact prefixLift 2964035
  have htrace : WordTrace (prefixWord ++ tailWord_2964035) baseStart_2964035 baseEnd_2964035 := by
    simpa [prefixWord, tailWord_2964035, baseEnd_2964035] using wordTrace_append hprefix tailTrace_2964035
  have hstable : (prefixWord ++ tailWord_2964035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964035).length < 2 ^ (prefixWord ++ tailWord_2964035).sum := by decide
  have hdescent : baseEnd_2964035 < baseStart_2964035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964042 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_2964042 : Nat := 118140960795 + 2964042 * 2 ^ 59
def prefixEnd_2964042 : Nat := 4983230072969 + 3 ^ 40 * 2964042 * 2
def baseEnd_2964042 : Nat := 1521978226113997405743625

theorem tailTrace_2964042 : CollatzResearch.WordTrace tailWord_2964042 prefixEnd_2964042 1521978226113997405743625 := by
  unfold tailWord_2964042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27026873281947381729157595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72071662085193017944420253 27026873281947381729157595)
  ·
    refine ⟨40540309922921072593736393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27026873281947381729157595 40540309922921072593736393)
    ·
      refine ⟨30405232442190804445302295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40540309922921072593736393 30405232442190804445302295)
      ·
        refine ⟨45607848663286206667953443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30405232442190804445302295 45607848663286206667953443)
        ·
          refine ⟨68411772994929310001930165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45607848663286206667953443 68411772994929310001930165)
          ·
            refine ⟨6413603718274622812680953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68411772994929310001930165 6413603718274622812680953)
            ·
              refine ⟨4810202788705967109510715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6413603718274622812680953 4810202788705967109510715)
              ·
                refine ⟨7215304183058950664266073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810202788705967109510715 7215304183058950664266073)
                ·
                  refine ⟨5411478137294212998199555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7215304183058950664266073 5411478137294212998199555)
                  ·
                    refine ⟨8117217205941319497299333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5411478137294212998199555 8117217205941319497299333)
                    ·
                      refine ⟨1521978226113997405743625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8117217205941319497299333 1521978226113997405743625)
                      ·
                        rfl

theorem cell23_2964042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_2964042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964042 prefixEnd_2964042 := by exact prefixLift 2964042
  have htrace : WordTrace (prefixWord ++ tailWord_2964042) baseStart_2964042 baseEnd_2964042 := by
    simpa [prefixWord, tailWord_2964042, baseEnd_2964042] using wordTrace_append hprefix tailTrace_2964042
  have hstable : (prefixWord ++ tailWord_2964042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964042).length < 2 ^ (prefixWord ++ tailWord_2964042).sum := by decide
  have hdescent : baseEnd_2964042 < baseStart_2964042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964048 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 8]
def baseStart_2964048 : Nat := 118140960795 + 2964048 * 2 ^ 59
def prefixEnd_2964048 : Nat := 4983230072969 + 3 ^ 40 * 2964048 * 2
def baseEnd_2964048 : Nat := 169109034110880486918733

theorem tailTrace_2964048 : CollatzResearch.WordTrace tailWord_2964048 prefixEnd_2964048 169109034110880486918733 := by
  unfold tailWord_2964048
  simp only [CollatzResearch.WordTrace]
  refine ⟨54053855982883894970674399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72071807977178526627565865 54053855982883894970674399)
  ·
    refine ⟨81080783974325842456011599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54053855982883894970674399 81080783974325842456011599)
    ·
      refine ⟨121621175961488763684017399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81080783974325842456011599 121621175961488763684017399)
      ·
        refine ⟨182431763942233145526026099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121621175961488763684017399 182431763942233145526026099)
        ·
          refine ⟨273647645913349718289039149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182431763942233145526026099 273647645913349718289039149)
          ·
            refine ⟨102617867217506144358389681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273647645913349718289039149 102617867217506144358389681)
            ·
              refine ⟨76963400413129608268792261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102617867217506144358389681 76963400413129608268792261)
              ·
                refine ⟨14430637577461801550398549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76963400413129608268792261 14430637577461801550398549)
                ·
                  refine ⟨169109034110880486918733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14430637577461801550398549 169109034110880486918733)
                  ·
                    rfl

theorem cell23_2964048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_2964048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964048 prefixEnd_2964048 := by exact prefixLift 2964048
  have htrace : WordTrace (prefixWord ++ tailWord_2964048) baseStart_2964048 baseEnd_2964048 := by
    simpa [prefixWord, tailWord_2964048, baseEnd_2964048] using wordTrace_append hprefix tailTrace_2964048
  have hstable : (prefixWord ++ tailWord_2964048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964048).length < 2 ^ (prefixWord ++ tailWord_2964048).sum := by decide
  have hdescent : baseEnd_2964048 < baseStart_2964048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964065 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 6]
def baseStart_2964065 : Nat := 118140960795 + 2964065 * 2 ^ 59
def prefixEnd_2964065 : Nat := 4983230072969 + 3 ^ 40 * 2964065 * 2
def baseEnd_2964065 : Nat := 169110004018783423972891

theorem tailTrace_2964065 : CollatzResearch.WordTrace tailWord_2964065 prefixEnd_2964065 169110004018783423972891 := by
  unfold tailWord_2964065
  simp only [CollatzResearch.WordTrace]
  refine ⟨108108332006706201844717649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72072221337804134563145099 108108332006706201844717649)
  ·
    refine ⟨81081249005029651383538237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108108332006706201844717649 81081249005029651383538237)
    ·
      refine ⟨30405468376886119268826839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81081249005029651383538237 30405468376886119268826839)
      ·
        refine ⟨45608202565329178903240259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30405468376886119268826839 45608202565329178903240259)
        ·
          refine ⟨68412303847993768354860389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45608202565329178903240259 68412303847993768354860389)
          ·
            refine ⟨12827306971498831566536323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68412303847993768354860389 12827306971498831566536323)
            ·
              refine ⟨19240960457248247349804485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12827306971498831566536323 19240960457248247349804485)
              ·
                refine ⟨3607680085734046378088341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19240960457248247349804485 3607680085734046378088341)
                ·
                  refine ⟨169110004018783423972891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3607680085734046378088341 169110004018783423972891)
                  ·
                    rfl

theorem cell23_2964065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 6].length) (baseStart_2964065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964065 prefixEnd_2964065 := by exact prefixLift 2964065
  have htrace : WordTrace (prefixWord ++ tailWord_2964065) baseStart_2964065 baseEnd_2964065 := by
    simpa [prefixWord, tailWord_2964065, baseEnd_2964065] using wordTrace_append hprefix tailTrace_2964065
  have hstable : (prefixWord ++ tailWord_2964065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964065).length < 2 ^ (prefixWord ++ tailWord_2964065).sum := by decide
  have hdescent : baseEnd_2964065 < baseStart_2964065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964092 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_2964092 : Nat := 118140960795 + 2964092 * 2 ^ 59
def prefixEnd_2964092 : Nat := 4983230072969 + 3 ^ 40 * 2964092 * 2
def baseEnd_2964092 : Nat := 1522003900146722210118395

theorem tailTrace_2964092 : CollatzResearch.WordTrace tailWord_2964092 prefixEnd_2964092 1522003900146722210118395 := by
  unfold tailWord_2964092
  simp only [CollatzResearch.WordTrace]
  refine ⟨54054658388804192727975265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72072877851738923637300353 54054658388804192727975265)
  ·
    refine ⟨40540993791603144545981449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54054658388804192727975265 40540993791603144545981449)
    ·
      refine ⟨30405745343702358409486087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40540993791603144545981449 30405745343702358409486087)
      ·
        refine ⟨45608618015553537614229131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30405745343702358409486087 45608618015553537614229131)
        ·
          refine ⟨68412927023330306421343697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45608618015553537614229131 68412927023330306421343697)
          ·
            refine ⟨51309695267497729816007773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68412927023330306421343697 51309695267497729816007773)
            ·
              refine ⟨19241135725311648681002915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51309695267497729816007773 19241135725311648681002915)
              ·
                refine ⟨28861703587967473021504373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19241135725311648681002915 28861703587967473021504373)
                ·
                  refine ⟨2705784711371950595766035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28861703587967473021504373 2705784711371950595766035)
                  ·
                    refine ⟨4058677067057925893649053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705784711371950595766035 4058677067057925893649053)
                    ·
                      refine ⟨1522003900146722210118395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4058677067057925893649053 1522003900146722210118395)
                      ·
                        rfl

theorem cell23_2964092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_2964092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964092 prefixEnd_2964092 := by exact prefixLift 2964092
  have htrace : WordTrace (prefixWord ++ tailWord_2964092) baseStart_2964092 baseEnd_2964092 := by
    simpa [prefixWord, tailWord_2964092, baseEnd_2964092] using wordTrace_append hprefix tailTrace_2964092
  have hstable : (prefixWord ++ tailWord_2964092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964092).length < 2 ^ (prefixWord ++ tailWord_2964092).sum := by decide
  have hdescent : baseEnd_2964092 < baseStart_2964092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964125 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2964125 : Nat := 118140960795 + 2964125 * 2 ^ 59
def prefixEnd_2964125 : Nat := 4983230072969 + 3 ^ 40 * 2964125 * 2
def baseEnd_2964125 : Nat := 507340281669440193668581

theorem tailTrace_2964125 : CollatzResearch.WordTrace tailWord_2964125 prefixEnd_2964125 507340281669440193668581 := by
  unfold tailWord_2964125
  simp only [CollatzResearch.WordTrace]
  refine ⟨108110520386488832091901829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72073680257659221394601219 108110520386488832091901829)
  ·
    refine ⟨20270722572466656017231593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108110520386488832091901829 20270722572466656017231593)
    ·
      refine ⟨15203041929349992012923695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20270722572466656017231593 15203041929349992012923695)
      ·
        refine ⟨22804562894024988019385543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15203041929349992012923695 22804562894024988019385543)
        ·
          refine ⟨34206844341037482029078315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22804562894024988019385543 34206844341037482029078315)
          ·
            refine ⟨51310266511556223043617473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34206844341037482029078315 51310266511556223043617473)
            ·
              refine ⟨38482699883667167282713105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51310266511556223043617473 38482699883667167282713105)
              ·
                refine ⟨28862024912750375462034829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38482699883667167282713105 28862024912750375462034829)
                ·
                  refine ⟨10823259342281390798263061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28862024912750375462034829 10823259342281390798263061)
                  ·
                    refine ⟨507340281669440193668581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10823259342281390798263061 507340281669440193668581)
                    ·
                      rfl

theorem cell23_2964125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2964125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964125 prefixEnd_2964125 := by exact prefixLift 2964125
  have htrace : WordTrace (prefixWord ++ tailWord_2964125) baseStart_2964125 baseEnd_2964125 := by
    simpa [prefixWord, tailWord_2964125, baseEnd_2964125] using wordTrace_append hprefix tailTrace_2964125
  have hstable : (prefixWord ++ tailWord_2964125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964125).length < 2 ^ (prefixWord ++ tailWord_2964125).sum := by decide
  have hdescent : baseEnd_2964125 < baseStart_2964125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964126 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2964126 : Nat := 118140960795 + 2964126 * 2 ^ 59
def prefixEnd_2964126 : Nat := 4983230072969 + 3 ^ 40 * 2964126 * 2
def baseEnd_2964126 : Nat := 1522021358488975077093239

theorem tailTrace_2964126 : CollatzResearch.WordTrace tailWord_2964126 prefixEnd_2964126 1522021358488975077093239 := by
  unfold tailWord_2964126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513819607435651157836029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72073704572990139508458821 13513819607435651157836029)
  ·
    refine ⟨5067682352788369184188511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13513819607435651157836029 5067682352788369184188511)
    ·
      refine ⟨7601523529182553776282767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5067682352788369184188511 7601523529182553776282767)
      ·
        refine ⟨11402285293773830664424151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7601523529182553776282767 11402285293773830664424151)
        ·
          refine ⟨17103427940660745996636227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11402285293773830664424151 17103427940660745996636227)
          ·
            refine ⟨25655141910991118994954341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17103427940660745996636227 25655141910991118994954341)
            ·
              refine ⟨4810339108310834811553939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25655141910991118994954341 4810339108310834811553939)
              ·
                refine ⟨7215508662466252217330909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810339108310834811553939 7215508662466252217330909)
                ·
                  refine ⟨2705815748424844581499091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7215508662466252217330909 2705815748424844581499091)
                  ·
                    refine ⟨4058723622637266872248637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705815748424844581499091 4058723622637266872248637)
                    ·
                      refine ⟨1522021358488975077093239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4058723622637266872248637 1522021358488975077093239)
                      ·
                        rfl

theorem cell23_2964126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2964126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964126 prefixEnd_2964126 := by exact prefixLift 2964126
  have htrace : WordTrace (prefixWord ++ tailWord_2964126) baseStart_2964126 baseEnd_2964126 := by
    simpa [prefixWord, tailWord_2964126, baseEnd_2964126] using wordTrace_append hprefix tailTrace_2964126
  have hstable : (prefixWord ++ tailWord_2964126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964126).length < 2 ^ (prefixWord ++ tailWord_2964126).sum := by decide
  have hdescent : baseEnd_2964126 < baseStart_2964126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964149 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2964149 : Nat := 118140960795 + 2964149 * 2 ^ 59
def prefixEnd_2964149 : Nat := 4983230072969 + 3 ^ 40 * 2964149 * 2
def baseEnd_2964149 : Nat := 1522033168544028487105633

theorem tailTrace_2964149 : CollatzResearch.WordTrace tailWord_2964149 prefixEnd_2964149 1522033168544028487105633 := by
  unfold tailWord_2964149
  simp only [CollatzResearch.WordTrace]
  refine ⟨108111395738401884190775501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72074263825601256127183667 108111395738401884190775501)
  ·
    refine ⟨40541773401900706571540813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108111395738401884190775501 40541773401900706571540813)
    ·
      refine ⟨15203165025712764964327805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40541773401900706571540813 15203165025712764964327805)
      ·
        refine ⟨5701186884642286861622927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15203165025712764964327805 5701186884642286861622927)
        ·
          refine ⟨8551780326963430292434391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701186884642286861622927 8551780326963430292434391)
          ·
            refine ⟨12827670490445145438651587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551780326963430292434391 12827670490445145438651587)
            ·
              refine ⟨19241505735667718157977381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12827670490445145438651587 19241505735667718157977381)
              ·
                refine ⟨3607782325437697154620759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19241505735667718157977381 3607782325437697154620759)
                ·
                  refine ⟨5411673488156545731931139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607782325437697154620759 5411673488156545731931139)
                  ·
                    refine ⟨8117510232234818597896709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5411673488156545731931139 8117510232234818597896709)
                    ·
                      refine ⟨1522033168544028487105633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8117510232234818597896709 1522033168544028487105633)
                      ·
                        rfl

theorem cell23_2964149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2964149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964149 prefixEnd_2964149 := by exact prefixLift 2964149
  have htrace : WordTrace (prefixWord ++ tailWord_2964149) baseStart_2964149 baseEnd_2964149 := by
    simpa [prefixWord, tailWord_2964149, baseEnd_2964149] using wordTrace_append hprefix tailTrace_2964149
  have hstable : (prefixWord ++ tailWord_2964149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964149).length < 2 ^ (prefixWord ++ tailWord_2964149).sum := by decide
  have hdescent : baseEnd_2964149 < baseStart_2964149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964172 : List Nat := [2, 2, 1, 5, 1, 3, 9]
def baseStart_2964172 : Nat := 118140960795 + 2964172 * 2 ^ 59
def prefixEnd_2964172 : Nat := 4983230072969 + 3 ^ 40 * 2964172 * 2
def baseEnd_2964172 : Nat := 18790678748136813544667

theorem tailTrace_2964172 : CollatzResearch.WordTrace tailWord_2964172 prefixEnd_2964172 18790678748136813544667 := by
  unfold tailWord_2964172
  simp only [CollatzResearch.WordTrace]
  refine ⟨54056117308659279559431385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72074823078212372745908513 54056117308659279559431385)
  ·
    refine ⟨40542087981494459669573539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54056117308659279559431385 40542087981494459669573539)
    ·
      refine ⟨60813131972241689504360309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40542087981494459669573539 60813131972241689504360309)
      ·
        refine ⟨5701231122397658391033779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60813131972241689504360309 5701231122397658391033779)
        ·
          refine ⟨8551846683596487586550669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701231122397658391033779 8551846683596487586550669)
          ·
            refine ⟨3206942506348682844956501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8551846683596487586550669 3206942506348682844956501)
            ·
              refine ⟨18790678748136813544667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3206942506348682844956501 18790678748136813544667)
              ·
                rfl

theorem cell23_2964172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 9].length) (baseStart_2964172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964172 prefixEnd_2964172 := by exact prefixLift 2964172
  have htrace : WordTrace (prefixWord ++ tailWord_2964172) baseStart_2964172 baseEnd_2964172 := by
    simpa [prefixWord, tailWord_2964172, baseEnd_2964172] using wordTrace_append hprefix tailTrace_2964172
  have hstable : (prefixWord ++ tailWord_2964172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964172).length < 2 ^ (prefixWord ++ tailWord_2964172).sum := by decide
  have hdescent : baseEnd_2964172 < baseStart_2964172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964185 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_2964185 : Nat := 118140960795 + 2964185 * 2 ^ 59
def prefixEnd_2964185 : Nat := 4983230072969 + 3 ^ 40 * 2964185 * 2
def baseEnd_2964185 : Nat := 507350551282530115418489

theorem tailTrace_2964185 : CollatzResearch.WordTrace tailWord_2964185 prefixEnd_2964185 507350551282530115418489 := by
  unfold tailWord_2964185
  simp only [CollatzResearch.WordTrace]
  refine ⟨108112708766271462339086009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72075139177514308226057339 108112708766271462339086009)
  ·
    refine ⟨81084531574703596754314507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108112708766271462339086009 81084531574703596754314507)
    ·
      refine ⟨121626797362055395131471761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81084531574703596754314507 121626797362055395131471761)
      ·
        refine ⟨91220098021541546348603821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121626797362055395131471761 91220098021541546348603821)
        ·
          refine ⟨34207536758078079880726433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91220098021541546348603821 34207536758078079880726433)
          ·
            refine ⟨25655652568558559910544825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34207536758078079880726433 25655652568558559910544825)
            ·
              refine ⟨19241739426418919932908619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25655652568558559910544825 19241739426418919932908619)
              ·
                refine ⟨28862609139628379899362929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19241739426418919932908619 28862609139628379899362929)
                ·
                  refine ⟨21646956854721284924522197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28862609139628379899362929 21646956854721284924522197)
                  ·
                    refine ⟨507350551282530115418489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21646956854721284924522197 507350551282530115418489)
                    ·
                      rfl

theorem cell23_2964185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_2964185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964185 prefixEnd_2964185 := by exact prefixLift 2964185
  have htrace : WordTrace (prefixWord ++ tailWord_2964185) baseStart_2964185 baseEnd_2964185 := by
    simpa [prefixWord, tailWord_2964185, baseEnd_2964185] using wordTrace_append hprefix tailTrace_2964185
  have hstable : (prefixWord ++ tailWord_2964185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964185).length < 2 ^ (prefixWord ++ tailWord_2964185).sum := by decide
  have hdescent : baseEnd_2964185 < baseStart_2964185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964192 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 7, 2]
def baseStart_2964192 : Nat := 118140960795 + 2964192 * 2 ^ 59
def prefixEnd_2964192 : Nat := 4983230072969 + 3 ^ 40 * 2964192 * 2
def baseEnd_2964192 : Nat := 1522055248212171818867935

theorem tailTrace_2964192 : CollatzResearch.WordTrace tailWord_2964192 prefixEnd_2964192 1522055248212171818867935 := by
  unfold tailWord_2964192
  simp only [CollatzResearch.WordTrace]
  refine ⟨54056482038623051267295415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72075309384830735023060553 54056482038623051267295415)
  ·
    refine ⟨81084723057934576900943123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54056482038623051267295415 81084723057934576900943123)
    ·
      refine ⟨121627084586901865351414685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81084723057934576900943123 121627084586901865351414685)
      ·
        refine ⟨45610156720088199506780507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121627084586901865351414685 45610156720088199506780507)
        ·
          refine ⟨68415235080132299260170761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45610156720088199506780507 68415235080132299260170761)
          ·
            refine ⟨51311426310099224445128071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68415235080132299260170761 51311426310099224445128071)
            ·
              refine ⟨76967139465148836667692107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51311426310099224445128071 76967139465148836667692107)
              ·
                refine ⟨115450709197723255001538161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76967139465148836667692107 115450709197723255001538161)
                ·
                  refine ⟨86588031898292441251153621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115450709197723255001538161 86588031898292441251153621)
                  ·
                    refine ⟨2029406997616229091823913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86588031898292441251153621 2029406997616229091823913)
                    ·
                      refine ⟨1522055248212171818867935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029406997616229091823913 1522055248212171818867935)
                      ·
                        rfl

theorem cell23_2964192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_2964192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964192 prefixEnd_2964192 := by exact prefixLift 2964192
  have htrace : WordTrace (prefixWord ++ tailWord_2964192) baseStart_2964192 baseEnd_2964192 := by
    simpa [prefixWord, tailWord_2964192, baseEnd_2964192] using wordTrace_append hprefix tailTrace_2964192
  have hstable : (prefixWord ++ tailWord_2964192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964192).length < 2 ^ (prefixWord ++ tailWord_2964192).sum := by decide
  have hdescent : baseEnd_2964192 < baseStart_2964192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964209 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 3, 3, 2]
def baseStart_2964209 : Nat := 118140960795 + 2964209 * 2 ^ 59
def prefixEnd_2964209 : Nat := 4983230072969 + 3 ^ 40 * 2964209 * 2
def baseEnd_2964209 : Nat := 1522063977383298252355357

theorem tailTrace_2964209 : CollatzResearch.WordTrace tailWord_2964209 prefixEnd_2964209 1522063977383298252355357 := by
  unfold tailWord_2964209
  simp only [CollatzResearch.WordTrace]
  refine ⟨108113584118184514437959681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72075722745456342958639787 108113584118184514437959681)
  ·
    refine ⟨81085188088638385828469761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108113584118184514437959681 81085188088638385828469761)
    ·
      refine ⟨60813891066478789371352321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81085188088638385828469761 60813891066478789371352321)
      ·
        refine ⟨45610418299859092028514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60813891066478789371352321 45610418299859092028514241)
        ·
          refine ⟨34207813724894319021385681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45610418299859092028514241 34207813724894319021385681)
          ·
            refine ⟨25655860293670739266039261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34207813724894319021385681 25655860293670739266039261)
            ·
              refine ⟨9620947610126527224764723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25655860293670739266039261 9620947610126527224764723)
              ·
                refine ⟨14431421415189790837147085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620947610126527224764723 14431421415189790837147085)
                ·
                  refine ⟨5411783030696171563930157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14431421415189790837147085 5411783030696171563930157)
                  ·
                    refine ⟨2029418636511064336473809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5411783030696171563930157 2029418636511064336473809)
                    ·
                      refine ⟨1522063977383298252355357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029418636511064336473809 1522063977383298252355357)
                      ·
                        rfl

theorem cell23_2964209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_2964209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964209 prefixEnd_2964209 := by exact prefixLift 2964209
  have htrace : WordTrace (prefixWord ++ tailWord_2964209) baseStart_2964209 baseEnd_2964209 := by
    simpa [prefixWord, tailWord_2964209, baseEnd_2964209] using wordTrace_append hprefix tailTrace_2964209
  have hstable : (prefixWord ++ tailWord_2964209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964209).length < 2 ^ (prefixWord ++ tailWord_2964209).sum := by decide
  have hdescent : baseEnd_2964209 < baseStart_2964209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964213 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2964213 : Nat := 118140960795 + 2964213 * 2 ^ 59
def prefixEnd_2964213 : Nat := 4983230072969 + 3 ^ 40 * 2964213 * 2
def baseEnd_2964213 : Nat := 1522066031305916236705339

theorem tailTrace_2964213 : CollatzResearch.WordTrace tailWord_2964213 prefixEnd_2964213 1522066031305916236705339 := by
  unfold tailWord_2964213
  simp only [CollatzResearch.WordTrace]
  refine ⟨108113730010170023121105293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72075820006780015414070195 108113730010170023121105293)
  ·
    refine ⟨40542648753813758670414485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108113730010170023121105293 40542648753813758670414485)
    ·
      refine ⟨1900436660335019937675679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40542648753813758670414485 1900436660335019937675679)
      ·
        refine ⟨2850654990502529906513519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900436660335019937675679 2850654990502529906513519)
        ·
          refine ⟨4275982485753794859770279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850654990502529906513519 4275982485753794859770279)
          ·
            refine ⟨6413973728630692289655419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275982485753794859770279 6413973728630692289655419)
            ·
              refine ⟨9620960592946038434483129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413973728630692289655419 9620960592946038434483129)
              ·
                refine ⟨7215720444709528825862347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9620960592946038434483129 7215720444709528825862347)
                ·
                  refine ⟨10823580667064293238793521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7215720444709528825862347 10823580667064293238793521)
                  ·
                    refine ⟨8117685500298219929095141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10823580667064293238793521 8117685500298219929095141)
                    ·
                      refine ⟨1522066031305916236705339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8117685500298219929095141 1522066031305916236705339)
                      ·
                        rfl

theorem cell23_2964213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2964213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964213 prefixEnd_2964213 := by exact prefixLift 2964213
  have htrace : WordTrace (prefixWord ++ tailWord_2964213) baseStart_2964213 baseEnd_2964213 := by
    simpa [prefixWord, tailWord_2964213, baseEnd_2964213] using wordTrace_append hprefix tailTrace_2964213
  have hstable : (prefixWord ++ tailWord_2964213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964213).length < 2 ^ (prefixWord ++ tailWord_2964213).sum := by decide
  have hdescent : baseEnd_2964213 < baseStart_2964213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964215 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 4, 6]
def baseStart_2964215 : Nat := 118140960795 + 2964215 * 2 ^ 59
def prefixEnd_2964215 : Nat := 4983230072969 + 3 ^ 40 * 2964215 * 2
def baseEnd_2964215 : Nat := 507355686089075076293443

theorem tailTrace_2964215 : CollatzResearch.WordTrace tailWord_2964215 prefixEnd_2964215 507355686089075076293443 := by
  unfold tailWord_2964215
  simp only [CollatzResearch.WordTrace]
  refine ⟨108113802956162777462678099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72075868637441851641785399 108113802956162777462678099)
  ·
    refine ⟨162170704434244166194017149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108113802956162777462678099 162170704434244166194017149)
    ·
      refine ⟨60814014162841562322756431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162170704434244166194017149 60814014162841562322756431)
      ·
        refine ⟨91221021244262343484134647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60814014162841562322756431 91221021244262343484134647)
        ·
          refine ⟨136831531866393515226201971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91221021244262343484134647 136831531866393515226201971)
          ·
            refine ⟨205247297799590272839302957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136831531866393515226201971 205247297799590272839302957)
            ·
              refine ⟨76967736674846352314738609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205247297799590272839302957 76967736674846352314738609)
              ·
                refine ⟨57725802506134764236053957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76967736674846352314738609 57725802506134764236053957)
                ·
                  refine ⟨10823587969900268294260117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57725802506134764236053957 10823587969900268294260117)
                  ·
                    refine ⟨507355686089075076293443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10823587969900268294260117 507355686089075076293443)
                    ·
                      rfl

theorem cell23_2964215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_2964215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964215 prefixEnd_2964215 := by exact prefixLift 2964215
  have htrace : WordTrace (prefixWord ++ tailWord_2964215) baseStart_2964215 baseEnd_2964215 := by
    simpa [prefixWord, tailWord_2964215, baseEnd_2964215] using wordTrace_append hprefix tailTrace_2964215
  have hstable : (prefixWord ++ tailWord_2964215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964215).length < 2 ^ (prefixWord ++ tailWord_2964215).sum := by decide
  have hdescent : baseEnd_2964215 < baseStart_2964215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964235 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_2964235 : Nat := 118140960795 + 2964235 * 2 ^ 59
def prefixEnd_2964235 : Nat := 4983230072969 + 3 ^ 40 * 2964235 * 2
def baseEnd_2964235 : Nat := 1522077327880315150630237

theorem tailTrace_2964235 : CollatzResearch.WordTrace tailWord_2964235 prefixEnd_2964235 1522077327880315150630237 := by
  unfold tailWord_2964235
  simp only [CollatzResearch.WordTrace]
  refine ⟨108114532416090320878406159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72076354944060213918937439 108114532416090320878406159)
  ·
    refine ⟨162171798624135481317609239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108114532416090320878406159 162171798624135481317609239)
    ·
      refine ⟨243257697936203221976413859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162171798624135481317609239 243257697936203221976413859)
      ·
        refine ⟨364886546904304832964620789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243257697936203221976413859 364886546904304832964620789)
        ·
          refine ⟨34208113772278578090433199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364886546904304832964620789 34208113772278578090433199)
          ·
            refine ⟨51312170658417867135649799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34208113772278578090433199 51312170658417867135649799)
            ·
              refine ⟨76968255987626800703474699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51312170658417867135649799 76968255987626800703474699)
              ·
                refine ⟨115452383981440201055212049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76968255987626800703474699 115452383981440201055212049)
                ·
                  refine ⟨86589287986080150791409037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115452383981440201055212049 86589287986080150791409037)
                  ·
                    refine ⟨32470982994780056546778389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86589287986080150791409037 32470982994780056546778389)
                    ·
                      refine ⟨1522077327880315150630237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32470982994780056546778389 1522077327880315150630237)
                      ·
                        rfl

theorem cell23_2964235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_2964235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964235 prefixEnd_2964235 := by exact prefixLift 2964235
  have htrace : WordTrace (prefixWord ++ tailWord_2964235) baseStart_2964235 baseEnd_2964235 := by
    simpa [prefixWord, tailWord_2964235, baseEnd_2964235] using wordTrace_append hprefix tailTrace_2964235
  have hstable : (prefixWord ++ tailWord_2964235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964235).length < 2 ^ (prefixWord ++ tailWord_2964235).sum := by decide
  have hdescent : baseEnd_2964235 < baseStart_2964235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964252 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2964252 : Nat := 118140960795 + 2964252 * 2 ^ 59
def prefixEnd_2964252 : Nat := 4983230072969 + 3 ^ 40 * 2964252 * 2
def baseEnd_2964252 : Nat := 1522086057051441584117659

theorem tailTrace_2964252 : CollatzResearch.WordTrace tailWord_2964252 prefixEnd_2964252 1522086057051441584117659 := by
  unfold tailWord_2964252
  simp only [CollatzResearch.WordTrace]
  refine ⟨54057576228514366390887505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72076768304685821854516673 54057576228514366390887505)
  ·
    refine ⟨40543182171385774793165629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54057576228514366390887505 40543182171385774793165629)
    ·
      refine ⟨15203693314269665547437111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40543182171385774793165629 15203693314269665547437111)
      ·
        refine ⟨22805539971404498321155667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15203693314269665547437111 22805539971404498321155667)
        ·
          refine ⟨34208309957106747481733501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22805539971404498321155667 34208309957106747481733501)
          ·
            refine ⟨12828116233915030305650063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34208309957106747481733501 12828116233915030305650063)
            ·
              refine ⟨19242174350872545458475095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12828116233915030305650063 19242174350872545458475095)
              ·
                refine ⟨28863261526308818187712643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19242174350872545458475095 28863261526308818187712643)
                ·
                  refine ⟨43294892289463227281568965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28863261526308818187712643 43294892289463227281568965)
                  ·
                    refine ⟨8117792304274355115294181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43294892289463227281568965 8117792304274355115294181)
                    ·
                      refine ⟨1522086057051441584117659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8117792304274355115294181 1522086057051441584117659)
                      ·
                        rfl

theorem cell23_2964252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2964252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964252 prefixEnd_2964252 := by exact prefixLift 2964252
  have htrace : WordTrace (prefixWord ++ tailWord_2964252) baseStart_2964252 baseEnd_2964252 := by
    simpa [prefixWord, tailWord_2964252, baseEnd_2964252] using wordTrace_append hprefix tailTrace_2964252
  have hstable : (prefixWord ++ tailWord_2964252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964252).length < 2 ^ (prefixWord ++ tailWord_2964252).sum := by decide
  have hdescent : baseEnd_2964252 < baseStart_2964252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964256 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 1, 4, 2]
def baseStart_2964256 : Nat := 118140960795 + 2964256 * 2 ^ 59
def prefixEnd_2964256 : Nat := 4983230072969 + 3 ^ 40 * 2964256 * 2
def baseEnd_2964256 : Nat := 1522088110974059568467641

theorem tailTrace_2964256 : CollatzResearch.WordTrace tailWord_2964256 prefixEnd_2964256 1522088110974059568467641 := by
  unfold tailWord_2964256
  simp only [CollatzResearch.WordTrace]
  refine ⟨54057649174507120732460311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72076865566009494309947081 54057649174507120732460311)
  ·
    refine ⟨81086473761760681098690467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54057649174507120732460311 81086473761760681098690467)
    ·
      refine ⟨121629710642641021648035701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81086473761760681098690467 121629710642641021648035701)
      ·
        refine ⟨11402785372747595779503347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121629710642641021648035701 11402785372747595779503347)
        ·
          refine ⟨17104178059121393669255021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11402785372747595779503347 17104178059121393669255021)
          ·
            refine ⟨6414066772170522625970633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17104178059121393669255021 6414066772170522625970633)
            ·
              refine ⟨4810550079127891969477975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6414066772170522625970633 4810550079127891969477975)
              ·
                refine ⟨7215825118691837954216963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810550079127891969477975 7215825118691837954216963)
                ·
                  refine ⟨10823737678037756931325445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7215825118691837954216963 10823737678037756931325445)
                  ·
                    refine ⟨2029450814632079424623521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10823737678037756931325445 2029450814632079424623521)
                    ·
                      refine ⟨1522088110974059568467641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029450814632079424623521 1522088110974059568467641)
                      ·
                        rfl

theorem cell23_2964256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_2964256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964256 prefixEnd_2964256 := by exact prefixLift 2964256
  have htrace : WordTrace (prefixWord ++ tailWord_2964256) baseStart_2964256 baseEnd_2964256 := by
    simpa [prefixWord, tailWord_2964256, baseEnd_2964256] using wordTrace_append hprefix tailTrace_2964256
  have hstable : (prefixWord ++ tailWord_2964256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964256).length < 2 ^ (prefixWord ++ tailWord_2964256).sum := by decide
  have hdescent : baseEnd_2964256 < baseStart_2964256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964265 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_2964265 : Nat := 118140960795 + 2964265 * 2 ^ 59
def prefixEnd_2964265 : Nat := 4983230072969 + 3 ^ 40 * 2964265 * 2
def baseEnd_2964265 : Nat := 1522092732299950033255099

theorem tailTrace_2964265 : CollatzResearch.WordTrace tailWord_2964265 prefixEnd_2964265 1522092732299950033255099 := by
  unfold tailWord_2964265
  simp only [CollatzResearch.WordTrace]
  refine ⟨108115626605981636001998249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72077084403987757334665499 108115626605981636001998249)
  ·
    refine ⟨81086719954486227001498687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108115626605981636001998249 81086719954486227001498687)
    ·
      refine ⟨121630079931729340502248031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81086719954486227001498687 121630079931729340502248031)
      ·
        refine ⟨182445119897594010753372047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121630079931729340502248031 182445119897594010753372047)
        ·
          refine ⟨273667679846391016130058071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182445119897594010753372047 273667679846391016130058071)
          ·
            refine ⟨410501519769586524195087107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273667679846391016130058071 410501519769586524195087107)
            ·
              refine ⟨615752279654379786292630661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410501519769586524195087107 615752279654379786292630661)
              ·
                refine ⟨115453552435196209929868249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615752279654379786292630661 115453552435196209929868249)
                ·
                  refine ⟨86590164326397157447401187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115453552435196209929868249 86590164326397157447401187)
                  ·
                    refine ⟨129885246489595736171101781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86590164326397157447401187 129885246489595736171101781)
                    ·
                      refine ⟨1522092732299950033255099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129885246489595736171101781 1522092732299950033255099)
                      ·
                        rfl

theorem cell23_2964265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_2964265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964265 prefixEnd_2964265 := by exact prefixLift 2964265
  have htrace : WordTrace (prefixWord ++ tailWord_2964265) baseStart_2964265 baseEnd_2964265 := by
    simpa [prefixWord, tailWord_2964265, baseEnd_2964265] using wordTrace_append hprefix tailTrace_2964265
  have hstable : (prefixWord ++ tailWord_2964265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964265).length < 2 ^ (prefixWord ++ tailWord_2964265).sum := by decide
  have hdescent : baseEnd_2964265 < baseStart_2964265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964279 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 5]
def baseStart_2964279 : Nat := 118140960795 + 2964279 * 2 ^ 59
def prefixEnd_2964279 : Nat := 4983230072969 + 3 ^ 40 * 2964279 * 2
def baseEnd_2964279 : Nat := 169122213447679219831115

theorem tailTrace_2964279 : CollatzResearch.WordTrace tailWord_2964279 prefixEnd_2964279 169122213447679219831115 := by
  unfold tailWord_2964279
  simp only [CollatzResearch.WordTrace]
  refine ⟨108116137227930916393007891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72077424818620610928671927 108116137227930916393007891)
  ·
    refine ⟨162174205841896374589511837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108116137227930916393007891 162174205841896374589511837)
    ·
      refine ⟨60815327190711140471066939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162174205841896374589511837 60815327190711140471066939)
      ·
        refine ⟨91222990786066710706600409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60815327190711140471066939 91222990786066710706600409)
        ·
          refine ⟨68417243089550033029950307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91222990786066710706600409 68417243089550033029950307)
          ·
            refine ⟨102625864634325049544925461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68417243089550033029950307 102625864634325049544925461)
            ·
              refine ⟨4810587404733986697418381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102625864634325049544925461 4810587404733986697418381)
              ·
                refine ⟨1803970276775245011531893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4810587404733986697418381 1803970276775245011531893)
                ·
                  refine ⟨169122213447679219831115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1803970276775245011531893 169122213447679219831115)
                  ·
                    rfl

theorem cell23_2964279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 5].length) (baseStart_2964279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964279 prefixEnd_2964279 := by exact prefixLift 2964279
  have htrace : WordTrace (prefixWord ++ tailWord_2964279) baseStart_2964279 baseEnd_2964279 := by
    simpa [prefixWord, tailWord_2964279, baseEnd_2964279] using wordTrace_append hprefix tailTrace_2964279
  have hstable : (prefixWord ++ tailWord_2964279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964279).length < 2 ^ (prefixWord ++ tailWord_2964279).sum := by decide
  have hdescent : baseEnd_2964279 < baseStart_2964279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964302 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2964302 : Nat := 118140960795 + 2964302 * 2 ^ 59
def prefixEnd_2964302 : Nat := 4983230072969 + 3 ^ 40 * 2964302 * 2
def baseEnd_2964302 : Nat := 1522111731084166388492429

theorem tailTrace_2964302 : CollatzResearch.WordTrace tailWord_2964302 prefixEnd_2964302 1522111731084166388492429 := by
  unfold tailWord_2964302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514622013355948915136895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72077984071231727547396773 13514622013355948915136895)
  ·
    refine ⟨20271933020033923372705343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13514622013355948915136895 20271933020033923372705343)
    ·
      refine ⟨30407899530050885059058015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20271933020033923372705343 30407899530050885059058015)
      ·
        refine ⟨45611849295076327588587023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30407899530050885059058015 45611849295076327588587023)
        ·
          refine ⟨68417773942614491382880535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45611849295076327588587023 68417773942614491382880535)
          ·
            refine ⟨102626660913921737074320803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68417773942614491382880535 102626660913921737074320803)
            ·
              refine ⟨153939991370882605611481205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102626660913921737074320803 153939991370882605611481205)
              ·
                refine ⟨14431874191020244276076363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153939991370882605611481205 14431874191020244276076363)
                ·
                  refine ⟨21647811286530366414114545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14431874191020244276076363 21647811286530366414114545)
                  ·
                    refine ⟨16235858464897774810585909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21647811286530366414114545 16235858464897774810585909)
                    ·
                      refine ⟨1522111731084166388492429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16235858464897774810585909 1522111731084166388492429)
                      ·
                        rfl

theorem cell23_2964302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2964302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964302 prefixEnd_2964302 := by exact prefixLift 2964302
  have htrace : WordTrace (prefixWord ++ tailWord_2964302) baseStart_2964302 baseEnd_2964302 := by
    simpa [prefixWord, tailWord_2964302, baseEnd_2964302] using wordTrace_append hprefix tailTrace_2964302
  have hstable : (prefixWord ++ tailWord_2964302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964302).length < 2 ^ (prefixWord ++ tailWord_2964302).sum := by decide
  have hdescent : baseEnd_2964302 < baseStart_2964302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964349 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_2964349 : Nat := 118140960795 + 2964349 * 2 ^ 59
def prefixEnd_2964349 : Nat := 4983230072969 + 3 ^ 40 * 2964349 * 2
def baseEnd_2964349 : Nat := 1522135864674927704604713

theorem tailTrace_2964349 : CollatzResearch.WordTrace tailWord_2964349 prefixEnd_2964349 1522135864674927704604713 := by
  unfold tailWord_2964349
  simp only [CollatzResearch.WordTrace]
  refine ⟨108118690337677318348056101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72079126891784878898704067 108118690337677318348056101)
  ·
    refine ⟨20272254438314497190260519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108118690337677318348056101 20272254438314497190260519)
    ·
      refine ⟨30408381657471745785390779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20272254438314497190260519 30408381657471745785390779)
      ·
        refine ⟨45612572486207618678086169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30408381657471745785390779 45612572486207618678086169)
        ·
          refine ⟨34209429364655714008564627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45612572486207618678086169 34209429364655714008564627)
          ·
            refine ⟨51314144046983571012846941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34209429364655714008564627 51314144046983571012846941)
            ·
              refine ⟨19242804017618839129817603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51314144046983571012846941 19242804017618839129817603)
              ·
                refine ⟨28864206026428258694726405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19242804017618839129817603 28864206026428258694726405)
                ·
                  refine ⟨5412038629955298505261201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28864206026428258694726405 5412038629955298505261201)
                  ·
                    refine ⟨4059028972466473878945901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5412038629955298505261201 4059028972466473878945901)
                    ·
                      refine ⟨1522135864674927704604713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059028972466473878945901 1522135864674927704604713)
                      ·
                        rfl

theorem cell23_2964349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_2964349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964349 prefixEnd_2964349 := by exact prefixLift 2964349
  have htrace : WordTrace (prefixWord ++ tailWord_2964349) baseStart_2964349 baseEnd_2964349 := by
    simpa [prefixWord, tailWord_2964349, baseEnd_2964349] using wordTrace_append hprefix tailTrace_2964349
  have hstable : (prefixWord ++ tailWord_2964349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964349).length < 2 ^ (prefixWord ++ tailWord_2964349).sum := by decide
  have hdescent : baseEnd_2964349 < baseStart_2964349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964436 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2964436 : Nat := 118140960795 + 2964436 * 2 ^ 59
def prefixEnd_2964436 : Nat := 4983230072969 + 3 ^ 40 * 2964436 * 2
def baseEnd_2964436 : Nat := 1522180537491868864216813

theorem tailTrace_2964436 : CollatzResearch.WordTrace tailWord_2964436 prefixEnd_2964436 1522180537491868864216813 := by
  unfold tailWord_2964436
  simp only [CollatzResearch.WordTrace]
  refine ⟨54060931744181066103236581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72081242325574754804315441 54060931744181066103236581)
  ·
    refine ⟨10136424702033949894356859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54060931744181066103236581 10136424702033949894356859)
    ·
      refine ⟨15204637053050924841535289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10136424702033949894356859 15204637053050924841535289)
      ·
        refine ⟨11403477789788193631151467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15204637053050924841535289 11403477789788193631151467)
        ·
          refine ⟨17105216684682290446727201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11403477789788193631151467 17105216684682290446727201)
          ·
            refine ⟨12828912513511717835045401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17105216684682290446727201 12828912513511717835045401)
            ·
              refine ⟨9621684385133788376284051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12828912513511717835045401 9621684385133788376284051)
              ·
                refine ⟨14432526577700682564426077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9621684385133788376284051 14432526577700682564426077)
                ·
                  refine ⟨5412197466637755961659779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14432526577700682564426077 5412197466637755961659779)
                  ·
                    refine ⟨8118296199956633942489669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5412197466637755961659779 8118296199956633942489669)
                    ·
                      refine ⟨1522180537491868864216813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8118296199956633942489669 1522180537491868864216813)
                      ·
                        rfl

theorem cell23_2964436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2964436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964436 prefixEnd_2964436 := by exact prefixLift 2964436
  have htrace : WordTrace (prefixWord ++ tailWord_2964436) baseStart_2964436 baseEnd_2964436 := by
    simpa [prefixWord, tailWord_2964436, baseEnd_2964436] using wordTrace_append hprefix tailTrace_2964436
  have hstable : (prefixWord ++ tailWord_2964436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964436).length < 2 ^ (prefixWord ++ tailWord_2964436).sum := by decide
  have hdescent : baseEnd_2964436 < baseStart_2964436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964450 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2964450 : Nat := 118140960795 + 2964450 * 2 ^ 59
def prefixEnd_2964450 : Nat := 4983230072969 + 3 ^ 40 * 2964450 * 2
def baseEnd_2964450 : Nat := 507395908740343936480583

theorem tailTrace_2964450 : CollatzResearch.WordTrace tailWord_2964450 prefixEnd_2964450 507395908740343936480583 := by
  unfold tailWord_2964450
  simp only [CollatzResearch.WordTrace]
  refine ⟨27030593527577853149370701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72081582740207608398321869 27030593527577853149370701)
  ·
    refine ⟨10136472572841694931014013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27030593527577853149370701 10136472572841694931014013)
    ·
      refine ⟨3801177214815635599130255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10136472572841694931014013 3801177214815635599130255)
      ·
        refine ⟨5701765822223453398695383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801177214815635599130255 5701765822223453398695383)
        ·
          refine ⟨8552648733335180098043075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701765822223453398695383 8552648733335180098043075)
          ·
            refine ⟨12828973100002770147064613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552648733335180098043075 12828973100002770147064613)
            ·
              refine ⟨2405432456250519402574615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12828973100002770147064613 2405432456250519402574615)
              ·
                refine ⟨3608148684375779103861923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405432456250519402574615 3608148684375779103861923)
                ·
                  refine ⟨5412223026563668655792885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608148684375779103861923 5412223026563668655792885)
                  ·
                    refine ⟨507395908740343936480583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5412223026563668655792885 507395908740343936480583)
                    ·
                      rfl

theorem cell23_2964450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2964450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964450 prefixEnd_2964450 := by exact prefixLift 2964450
  have htrace : WordTrace (prefixWord ++ tailWord_2964450) baseStart_2964450 baseEnd_2964450 := by
    simpa [prefixWord, tailWord_2964450, baseEnd_2964450] using wordTrace_append hprefix tailTrace_2964450
  have hstable : (prefixWord ++ tailWord_2964450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964450).length < 2 ^ (prefixWord ++ tailWord_2964450).sum := by decide
  have hdescent : baseEnd_2964450 < baseStart_2964450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964463 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 2, 4]
def baseStart_2964463 : Nat := 118140960795 + 2964463 * 2 ^ 59
def prefixEnd_2964463 : Nat := 4983230072969 + 3 ^ 40 * 2964463 * 2
def baseEnd_2964463 : Nat := 507398133823180086193063

theorem tailTrace_2964463 : CollatzResearch.WordTrace tailWord_2964463 prefixEnd_2964463 507398133823180086193063 := by
  unfold tailWord_2964463
  simp only [CollatzResearch.WordTrace]
  refine ⟨108122848259264315817706043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72081898839509543878470695 108122848259264315817706043)
  ·
    refine ⟨162184272388896473726559065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108122848259264315817706043 162184272388896473726559065)
    ·
      refine ⟨121638204291672355294919299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162184272388896473726559065 121638204291672355294919299)
      ·
        refine ⟨182457306437508532942378949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121638204291672355294919299 182457306437508532942378949)
        ·
          refine ⟨34210744957032849926696053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182457306437508532942378949 34210744957032849926696053)
          ·
            refine ⟨3207257339721829680627755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34210744957032849926696053 3207257339721829680627755)
            ·
              refine ⟨4810886009582744520941633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207257339721829680627755 4810886009582744520941633)
              ·
                refine ⟨3608164507187058390706225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810886009582744520941633 3608164507187058390706225)
                ·
                  refine ⟨2706123380390293793029669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608164507187058390706225 2706123380390293793029669)
                  ·
                    refine ⟨507398133823180086193063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706123380390293793029669 507398133823180086193063)
                    ·
                      rfl

theorem cell23_2964463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_2964463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964463 prefixEnd_2964463 := by exact prefixLift 2964463
  have htrace : WordTrace (prefixWord ++ tailWord_2964463) baseStart_2964463 baseEnd_2964463 := by
    simpa [prefixWord, tailWord_2964463, baseEnd_2964463] using wordTrace_append hprefix tailTrace_2964463
  have hstable : (prefixWord ++ tailWord_2964463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964463).length < 2 ^ (prefixWord ++ tailWord_2964463).sum := by decide
  have hdescent : baseEnd_2964463 < baseStart_2964463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964470 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_2964470 : Nat := 118140960795 + 2964470 * 2 ^ 59
def prefixEnd_2964470 : Nat := 4983230072969 + 3 ^ 40 * 2964470 * 2
def baseEnd_2964470 : Nat := 1522197995834121731191657

theorem tailTrace_2964470 : CollatzResearch.WordTrace tailWord_2964470 prefixEnd_2964470 1522197995834121731191657 := by
  unfold tailWord_2964470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757693973139934750825679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72082069046825970675473909 6757693973139934750825679)
  ·
    refine ⟨10136540959709902126238519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6757693973139934750825679 10136540959709902126238519)
    ·
      refine ⟨15204811439564853189357779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10136540959709902126238519 15204811439564853189357779)
      ·
        refine ⟨22807217159347279784036669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15204811439564853189357779 22807217159347279784036669)
        ·
          refine ⟨8552706434755229919013751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22807217159347279784036669 8552706434755229919013751)
          ·
            refine ⟨12829059652132844878520627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552706434755229919013751 12829059652132844878520627)
            ·
              refine ⟨19243589478199267317780941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12829059652132844878520627 19243589478199267317780941)
              ·
                refine ⟨7216346054324725244167853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19243589478199267317780941 7216346054324725244167853)
                ·
                  refine ⟨2706129770371771966562945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7216346054324725244167853 2706129770371771966562945)
                  ·
                    refine ⟨2029597327778828974922209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2706129770371771966562945 2029597327778828974922209)
                    ·
                      refine ⟨1522197995834121731191657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029597327778828974922209 1522197995834121731191657)
                      ·
                        rfl

theorem cell23_2964470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_2964470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964470 prefixEnd_2964470 := by exact prefixLift 2964470
  have htrace : WordTrace (prefixWord ++ tailWord_2964470) baseStart_2964470 baseEnd_2964470 := by
    simpa [prefixWord, tailWord_2964470, baseEnd_2964470] using wordTrace_append hprefix tailTrace_2964470
  have hstable : (prefixWord ++ tailWord_2964470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964470).length < 2 ^ (prefixWord ++ tailWord_2964470).sum := by decide
  have hdescent : baseEnd_2964470 < baseStart_2964470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964498 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2964498 : Nat := 118140960795 + 2964498 * 2 ^ 59
def prefixEnd_2964498 : Nat := 4983230072969 + 3 ^ 40 * 2964498 * 2
def baseEnd_2964498 : Nat := 1522212373292447621641529

theorem tailTrace_2964498 : CollatzResearch.WordTrace tailWord_2964498 prefixEnd_2964498 1522212373292447621641529 := by
  unfold tailWord_2964498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27031031203534379198807537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72082749876091677863486765 27031031203534379198807537)
  ·
    refine ⟨20273273402650784399105653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27031031203534379198807537 20273273402650784399105653)
    ·
      refine ⟨1900619381498511037416155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20273273402650784399105653 1900619381498511037416155)
      ·
        refine ⟨2850929072247766556124233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900619381498511037416155 2850929072247766556124233)
        ·
          refine ⟨2138196804185824917093175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2850929072247766556124233 2138196804185824917093175)
          ·
            refine ⟨3207295206278737375639763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138196804185824917093175 3207295206278737375639763)
            ·
              refine ⟨4810942809418106063459645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207295206278737375639763 4810942809418106063459645)
              ·
                refine ⟨1804103553531789773797367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4810942809418106063459645 1804103553531789773797367)
                ·
                  refine ⟨2706155330297684660696051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804103553531789773797367 2706155330297684660696051)
                  ·
                    refine ⟨4059232995446526991044077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706155330297684660696051 4059232995446526991044077)
                    ·
                      refine ⟨1522212373292447621641529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059232995446526991044077 1522212373292447621641529)
                      ·
                        rfl

theorem cell23_2964498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2964498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964498 prefixEnd_2964498 := by exact prefixLift 2964498
  have htrace : WordTrace (prefixWord ++ tailWord_2964498) baseStart_2964498 baseEnd_2964498 := by
    simpa [prefixWord, tailWord_2964498, baseEnd_2964498] using wordTrace_append hprefix tailTrace_2964498
  have hstable : (prefixWord ++ tailWord_2964498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964498).length < 2 ^ (prefixWord ++ tailWord_2964498).sum := by decide
  have hdescent : baseEnd_2964498 < baseStart_2964498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964503 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2964503 : Nat := 118140960795 + 2964503 * 2 ^ 59
def prefixEnd_2964503 : Nat := 4983230072969 + 3 ^ 40 * 2964503 * 2
def baseEnd_2964503 : Nat := 1522214940695720102079005

theorem tailTrace_2964503 : CollatzResearch.WordTrace tailWord_2964503 prefixEnd_2964503 1522214940695720102079005 := by
  unfold tailWord_2964503
  simp only [CollatzResearch.WordTrace]
  refine ⟨108124307179119402649162163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72082871452746268432774775 108124307179119402649162163)
  ·
    refine ⟨162186460768679103973743245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108124307179119402649162163 162186460768679103973743245)
    ·
      refine ⟨60819922788254663990153717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162186460768679103973743245 60819922788254663990153717)
      ·
        refine ⟨5701867761398874749076911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60819922788254663990153717 5701867761398874749076911)
        ·
          refine ⟨8552801642098312123615367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701867761398874749076911 8552801642098312123615367)
          ·
            refine ⟨12829202463147468185423051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552801642098312123615367 12829202463147468185423051)
            ·
              refine ⟨19243803694721202278134577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12829202463147468185423051 19243803694721202278134577)
              ·
                refine ⟨14432852771040901708600933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19243803694721202278134577 14432852771040901708600933)
                ·
                  refine ⟨2706159894570169070362675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14432852771040901708600933 2706159894570169070362675)
                  ·
                    refine ⟨4059239841855253605544013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706159894570169070362675 4059239841855253605544013)
                    ·
                      refine ⟨1522214940695720102079005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059239841855253605544013 1522214940695720102079005)
                      ·
                        rfl

theorem cell23_2964503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2964503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964503 prefixEnd_2964503 := by exact prefixLift 2964503
  have htrace : WordTrace (prefixWord ++ tailWord_2964503) baseStart_2964503 baseEnd_2964503 := by
    simpa [prefixWord, tailWord_2964503, baseEnd_2964503] using wordTrace_append hprefix tailTrace_2964503
  have hstable : (prefixWord ++ tailWord_2964503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964503).length < 2 ^ (prefixWord ++ tailWord_2964503).sum := by decide
  have hdescent : baseEnd_2964503 < baseStart_2964503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964526 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2964526 : Nat := 118140960795 + 2964526 * 2 ^ 59
def prefixEnd_2964526 : Nat := 4983230072969 + 3 ^ 40 * 2964526 * 2
def baseEnd_2964526 : Nat := 1522226750750773512091399

theorem tailTrace_2964526 : CollatzResearch.WordTrace tailWord_2964526 prefixEnd_2964526 1522226750750773512091399 := by
  unfold tailWord_2964526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515643257254509697156179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72083430705357385051499621 13515643257254509697156179)
  ·
    refine ⟨20273464885881764545734269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13515643257254509697156179 20273464885881764545734269)
    ·
      refine ⟨7602549332205661704650351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20273464885881764545734269 7602549332205661704650351)
      ·
        refine ⟨11403823998308492556975527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7602549332205661704650351 11403823998308492556975527)
        ·
          refine ⟨17105735997462738835463291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11403823998308492556975527 17105735997462738835463291)
          ·
            refine ⟨25658603996194108253194937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17105735997462738835463291 25658603996194108253194937)
            ·
              refine ⟨19243952997145581189896203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25658603996194108253194937 19243952997145581189896203)
              ·
                refine ⟨28865929495718371784844305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19243952997145581189896203 28865929495718371784844305)
                ·
                  refine ⟨21649447121788778838633229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28865929495718371784844305 21649447121788778838633229)
                  ·
                    refine ⟨8118542670670792064487461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21649447121788778838633229 8118542670670792064487461)
                    ·
                      refine ⟨1522226750750773512091399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8118542670670792064487461 1522226750750773512091399)
                      ·
                        rfl

theorem cell23_2964526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2964526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964526 prefixEnd_2964526 := by exact prefixLift 2964526
  have htrace : WordTrace (prefixWord ++ tailWord_2964526) baseStart_2964526 baseEnd_2964526 := by
    simpa [prefixWord, tailWord_2964526, baseEnd_2964526] using wordTrace_append hprefix tailTrace_2964526
  have hstable : (prefixWord ++ tailWord_2964526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964526).length < 2 ^ (prefixWord ++ tailWord_2964526).sum := by decide
  have hdescent : baseEnd_2964526 < baseStart_2964526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964529 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2964529 : Nat := 118140960795 + 2964529 * 2 ^ 59
def prefixEnd_2964529 : Nat := 4983230072969 + 3 ^ 40 * 2964529 * 2
def baseEnd_2964529 : Nat := 1522228291192737000353885

theorem tailTrace_2964529 : CollatzResearch.WordTrace tailWord_2964529 prefixEnd_2964529 1522228291192737000353885 := by
  unfold tailWord_2964529
  simp only [CollatzResearch.WordTrace]
  refine ⟨108125255477025209089608641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72083503651350139393072427 108125255477025209089608641)
  ·
    refine ⟨81093941607768906817206481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108125255477025209089608641 81093941607768906817206481)
    ·
      refine ⟨60820456205826680112904861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81093941607768906817206481 60820456205826680112904861)
      ·
        refine ⟨22807671077185005042339323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60820456205826680112904861 22807671077185005042339323)
        ·
          refine ⟨34211506615777507563508985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22807671077185005042339323 34211506615777507563508985)
          ·
            refine ⟨25658629961833130672631739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34211506615777507563508985 25658629961833130672631739)
            ·
              refine ⟨38487944942749696008947609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25658629961833130672631739 38487944942749696008947609)
              ·
                refine ⟨28865958707062272006710707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38487944942749696008947609 28865958707062272006710707)
                ·
                  refine ⟨43298938060593408010066061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28865958707062272006710707 43298938060593408010066061)
                  ·
                    refine ⟨16237101772722528003774773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43298938060593408010066061 16237101772722528003774773)
                    ·
                      refine ⟨1522228291192737000353885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16237101772722528003774773 1522228291192737000353885)
                      ·
                        rfl

theorem cell23_2964529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2964529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964529 prefixEnd_2964529 := by exact prefixLift 2964529
  have htrace : WordTrace (prefixWord ++ tailWord_2964529) baseStart_2964529 baseEnd_2964529 := by
    simpa [prefixWord, tailWord_2964529, baseEnd_2964529] using wordTrace_append hprefix tailTrace_2964529
  have hstable : (prefixWord ++ tailWord_2964529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964529).length < 2 ^ (prefixWord ++ tailWord_2964529).sum := by decide
  have hdescent : baseEnd_2964529 < baseStart_2964529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964537 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2964537 : Nat := 118140960795 + 2964537 * 2 ^ 59
def prefixEnd_2964537 : Nat := 4983230072969 + 3 ^ 40 * 2964537 * 2
def baseEnd_2964537 : Nat := 1522232399037972969053849

theorem tailTrace_2964537 : CollatzResearch.WordTrace tailWord_2964537 prefixEnd_2964537 1522232399037972969053849 := by
  unfold tailWord_2964537
  simp only [CollatzResearch.WordTrace]
  refine ⟨108125547260996226455899865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72083698173997484303933243 108125547260996226455899865)
  ·
    refine ⟨81094160445747169841924899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108125547260996226455899865 81094160445747169841924899)
    ·
      refine ⟨121641240668620754762887349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81094160445747169841924899 121641240668620754762887349)
      ·
        refine ⟨11403866312683195759020689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121641240668620754762887349 11403866312683195759020689)
        ·
          refine ⟨8552899734512396819265517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11403866312683195759020689 8552899734512396819265517)
          ·
            refine ⟨3207337400442148807224569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8552899734512396819265517 3207337400442148807224569)
            ·
              refine ⟨2405503050331611605418427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3207337400442148807224569 2405503050331611605418427)
              ·
                refine ⟨3608254575497417408127641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405503050331611605418427 3608254575497417408127641)
                ·
                  refine ⟨2706190931623063056095731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608254575497417408127641 2706190931623063056095731)
                  ·
                    refine ⟨4059286397434594584143597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706190931623063056095731 4059286397434594584143597)
                    ·
                      refine ⟨1522232399037972969053849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059286397434594584143597 1522232399037972969053849)
                      ·
                        rfl

theorem cell23_2964537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2964537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964537 prefixEnd_2964537 := by exact prefixLift 2964537
  have htrace : WordTrace (prefixWord ++ tailWord_2964537) baseStart_2964537 baseEnd_2964537 := by
    simpa [prefixWord, tailWord_2964537, baseEnd_2964537] using wordTrace_append hprefix tailTrace_2964537
  have hstable : (prefixWord ++ tailWord_2964537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964537).length < 2 ^ (prefixWord ++ tailWord_2964537).sum := by decide
  have hdescent : baseEnd_2964537 < baseStart_2964537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964549 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 7]
def baseStart_2964549 : Nat := 118140960795 + 2964549 * 2 ^ 59
def prefixEnd_2964549 : Nat := 4983230072969 + 3 ^ 40 * 2964549 * 2
def baseEnd_2964549 : Nat := 169137617867314102455977

theorem tailTrace_2964549 : CollatzResearch.WordTrace tailWord_2964549 prefixEnd_2964549 169137617867314102455977 := by
  unfold tailWord_2964549
  simp only [CollatzResearch.WordTrace]
  refine ⟨108125984936952752505336701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72083989957968501670224467 108125984936952752505336701)
  ·
    refine ⟨40547244351357282189501263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108125984936952752505336701 40547244351357282189501263)
    ·
      refine ⟨60820866527035923284251895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40547244351357282189501263 60820866527035923284251895)
      ·
        refine ⟨91231299790553884926377843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60820866527035923284251895 91231299790553884926377843)
        ·
          refine ⟨136846949685830827389566765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91231299790553884926377843 136846949685830827389566765)
          ·
            refine ⟨51317606132186560271087537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136846949685830827389566765 51317606132186560271087537)
            ·
              refine ⟨38488204599139920203315653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51317606132186560271087537 38488204599139920203315653)
              ·
                refine ⟨7216538362338735038121685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38488204599139920203315653 7216538362338735038121685)
                ·
                  refine ⟨169137617867314102455977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7216538362338735038121685 169137617867314102455977)
                  ·
                    rfl

theorem cell23_2964549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_2964549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964549 prefixEnd_2964549 := by exact prefixLift 2964549
  have htrace : WordTrace (prefixWord ++ tailWord_2964549) baseStart_2964549 baseEnd_2964549 := by
    simpa [prefixWord, tailWord_2964549, baseEnd_2964549] using wordTrace_append hprefix tailTrace_2964549
  have hstable : (prefixWord ++ tailWord_2964549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964549).length < 2 ^ (prefixWord ++ tailWord_2964549).sum := by decide
  have hdescent : baseEnd_2964549 < baseStart_2964549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964576 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_2964576 : Nat := 118140960795 + 2964576 * 2 ^ 59
def prefixEnd_2964576 : Nat := 4983230072969 + 3 ^ 40 * 2964576 * 2
def baseEnd_2964576 : Nat := 1522252424783498316466169

theorem tailTrace_2964576 : CollatzResearch.WordTrace tailWord_2964576 prefixEnd_2964576 1522252424783498316466169 := by
  unfold tailWord_2964576
  simp only [CollatzResearch.WordTrace]
  refine ⟨54063484853927468058284791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72084646471903290744379721 54063484853927468058284791)
  ·
    refine ⟨81095227280891202087427187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54063484853927468058284791 81095227280891202087427187)
    ·
      refine ⟨121642840921336803131140781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81095227280891202087427187 121642840921336803131140781)
      ·
        refine ⟨45616065345501301174177793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121642840921336803131140781 45616065345501301174177793)
        ·
          refine ⟨34212049009125975880633345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45616065345501301174177793 34212049009125975880633345)
          ·
            refine ⟨25659036756844481910475009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34212049009125975880633345 25659036756844481910475009)
            ·
              refine ⟨19244277567633361432856257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25659036756844481910475009 19244277567633361432856257)
              ·
                refine ⟨14433208175725021074642193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19244277567633361432856257 14433208175725021074642193)
                ·
                  refine ⟨10824906131793765805981645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14433208175725021074642193 10824906131793765805981645)
                  ·
                    refine ⟨4059339799422662177243117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10824906131793765805981645 4059339799422662177243117)
                    ·
                      refine ⟨1522252424783498316466169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059339799422662177243117 1522252424783498316466169)
                      ·
                        rfl

theorem cell23_2964576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_2964576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964576 prefixEnd_2964576 := by exact prefixLift 2964576
  have htrace : WordTrace (prefixWord ++ tailWord_2964576) baseStart_2964576 baseEnd_2964576 := by
    simpa [prefixWord, tailWord_2964576, baseEnd_2964576] using wordTrace_append hprefix tailTrace_2964576
  have hstable : (prefixWord ++ tailWord_2964576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964576).length < 2 ^ (prefixWord ++ tailWord_2964576).sum := by decide
  have hdescent : baseEnd_2964576 < baseStart_2964576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964579 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 3, 7]
def baseStart_2964579 : Nat := 118140960795 + 2964579 * 2 ^ 59
def prefixEnd_2964579 : Nat := 4983230072969 + 3 ^ 40 * 2964579 * 2
def baseEnd_2964579 : Nat := 507417988408487268242885

theorem tailTrace_2964579 : CollatzResearch.WordTrace tailWord_2964579 prefixEnd_2964579 507417988408487268242885 := by
  unfold tailWord_2964579
  simp only [CollatzResearch.WordTrace]
  refine ⟨108127079126844067628928791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72084719417896045085952527 108127079126844067628928791)
  ·
    refine ⟨162190618690266101443393187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108127079126844067628928791 162190618690266101443393187)
    ·
      refine ⟨243285928035399152165089781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162190618690266101443393187 243285928035399152165089781)
      ·
        refine ⟨22808055753318670515477167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243285928035399152165089781 22808055753318670515477167)
        ·
          refine ⟨34212083629978005773215751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22808055753318670515477167 34212083629978005773215751)
          ·
            refine ⟨51318125444967008659823627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34212083629978005773215751 51318125444967008659823627)
            ·
              refine ⟨76977188167450512989735441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51318125444967008659823627 76977188167450512989735441)
              ·
                refine ⟨57732891125587884742301581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76977188167450512989735441 57732891125587884742301581)
                ·
                  refine ⟨21649834172095456778363093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57732891125587884742301581 21649834172095456778363093)
                  ·
                    refine ⟨507417988408487268242885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21649834172095456778363093 507417988408487268242885)
                    ·
                      rfl

theorem cell23_2964579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_2964579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964579 prefixEnd_2964579 := by exact prefixLift 2964579
  have htrace : WordTrace (prefixWord ++ tailWord_2964579) baseStart_2964579 baseEnd_2964579 := by
    simpa [prefixWord, tailWord_2964579, baseEnd_2964579] using wordTrace_append hprefix tailTrace_2964579
  have hstable : (prefixWord ++ tailWord_2964579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964579).length < 2 ^ (prefixWord ++ tailWord_2964579).sum := by decide
  have hdescent : baseEnd_2964579 < baseStart_2964579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964583 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 5]
def baseStart_2964583 : Nat := 118140960795 + 2964583 * 2 ^ 59
def prefixEnd_2964583 : Nat := 4983230072969 + 3 ^ 40 * 2964583 * 2
def baseEnd_2964583 : Nat := 169139557683119976564293

theorem tailTrace_2964583 : CollatzResearch.WordTrace tailWord_2964583 prefixEnd_2964583 169139557683119976564293 := by
  unfold tailWord_2964583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108127225018829576312074403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72084816679219717541382935 108127225018829576312074403)
  ·
    refine ⟨162190837528244364468111605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108127225018829576312074403 162190837528244364468111605)
    ·
      refine ⟨15205391018272909168885463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162190837528244364468111605 15205391018272909168885463)
      ·
        refine ⟨22808086527409363753328195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15205391018272909168885463 22808086527409363753328195)
        ·
          refine ⟨34212129791114045629992293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22808086527409363753328195 34212129791114045629992293)
          ·
            refine ⟨6414774335833883555623555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34212129791114045629992293 6414774335833883555623555)
            ·
              refine ⟨9622161503750825333435333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6414774335833883555623555 9622161503750825333435333)
              ·
                refine ⟨1804155281953279750019125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9622161503750825333435333 1804155281953279750019125)
                ·
                  refine ⟨169139557683119976564293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1804155281953279750019125 169139557683119976564293)
                  ·
                    rfl

theorem cell23_2964583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 5].length) (baseStart_2964583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964583 prefixEnd_2964583 := by exact prefixLift 2964583
  have htrace : WordTrace (prefixWord ++ tailWord_2964583) baseStart_2964583 baseEnd_2964583 := by
    simpa [prefixWord, tailWord_2964583, baseEnd_2964583] using wordTrace_append hprefix tailTrace_2964583
  have hstable : (prefixWord ++ tailWord_2964583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964583).length < 2 ^ (prefixWord ++ tailWord_2964583).sum := by decide
  have hdescent : baseEnd_2964583 < baseStart_2964583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964666 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_2964666 : Nat := 118140960795 + 2964666 * 2 ^ 59
def prefixEnd_2964666 : Nat := 4983230072969 + 3 ^ 40 * 2964666 * 2
def baseEnd_2964666 : Nat := 1522298638042402964340755

theorem tailTrace_2964666 : CollatzResearch.WordTrace tailWord_2964666 prefixEnd_2964666 1522298638042402964340755 := by
  unfold tailWord_2964666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27032563069382220371836463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72086834851685920991563901 27032563069382220371836463)
  ·
    refine ⟨40548844604073330557754695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27032563069382220371836463 40548844604073330557754695)
    ·
      refine ⟨60823266906109995836632043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40548844604073330557754695 60823266906109995836632043)
      ·
        refine ⟨91234900359164993754948065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60823266906109995836632043 91234900359164993754948065)
        ·
          refine ⟨68426175269373745316211049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91234900359164993754948065 68426175269373745316211049)
          ·
            refine ⟨51319631452030308987158287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68426175269373745316211049 51319631452030308987158287)
            ·
              refine ⟨76979447178045463480737431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51319631452030308987158287 76979447178045463480737431)
              ·
                refine ⟨115469170767068195221106147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76979447178045463480737431 115469170767068195221106147)
                ·
                  refine ⟨173203756150602292831659221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115469170767068195221106147 173203756150602292831659221)
                  ·
                    refine ⟨4059463034779741238242013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 173203756150602292831659221 4059463034779741238242013)
                    ·
                      refine ⟨1522298638042402964340755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059463034779741238242013 1522298638042402964340755)
                      ·
                        rfl

theorem cell23_2964666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_2964666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964666 prefixEnd_2964666 := by exact prefixLift 2964666
  have htrace : WordTrace (prefixWord ++ tailWord_2964666) baseStart_2964666 baseEnd_2964666 := by
    simpa [prefixWord, tailWord_2964666, baseEnd_2964666] using wordTrace_append hprefix tailTrace_2964666
  have hstable : (prefixWord ++ tailWord_2964666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964666).length < 2 ^ (prefixWord ++ tailWord_2964666).sum := by decide
  have hdescent : baseEnd_2964666 < baseStart_2964666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964673 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 8]
def baseStart_2964673 : Nat := 118140960795 + 2964673 * 2 ^ 59
def prefixEnd_2964673 : Nat := 4983230072969 + 3 ^ 40 * 2964673 * 2
def baseEnd_2964673 : Nat := 169144692489664937439247

theorem tailTrace_2964673 : CollatzResearch.WordTrace tailWord_2964673 prefixEnd_2964673 169144692489664937439247 := by
  unfold tailWord_2964673
  simp only [CollatzResearch.WordTrace]
  refine ⟨108130507588503521682850673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72087005059002347788567115 108130507588503521682850673)
  ·
    refine ⟨81097880691377641262138005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108130507588503521682850673 81097880691377641262138005)
    ·
      refine ⟨3801463157408326934162719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81097880691377641262138005 3801463157408326934162719)
      ·
        refine ⟨5702194736112490401244079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801463157408326934162719 5702194736112490401244079)
        ·
          refine ⟨8553292104168735601866119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702194736112490401244079 8553292104168735601866119)
          ·
            refine ⟨12829938156253103402799179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553292104168735601866119 12829938156253103402799179)
            ·
              refine ⟨19244907234379655104198769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12829938156253103402799179 19244907234379655104198769)
              ·
                refine ⟨14433680425784741328149077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19244907234379655104198769 14433680425784741328149077)
                ·
                  refine ⟨169144692489664937439247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14433680425784741328149077 169144692489664937439247)
                  ·
                    rfl

theorem cell23_2964673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 8].length) (baseStart_2964673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964673 prefixEnd_2964673 := by exact prefixLift 2964673
  have htrace : WordTrace (prefixWord ++ tailWord_2964673) baseStart_2964673 baseEnd_2964673 := by
    simpa [prefixWord, tailWord_2964673, baseEnd_2964673] using wordTrace_append hprefix tailTrace_2964673
  have hstable : (prefixWord ++ tailWord_2964673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964673).length < 2 ^ (prefixWord ++ tailWord_2964673).sum := by decide
  have hdescent : baseEnd_2964673 < baseStart_2964673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964694 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2964694 : Nat := 118140960795 + 2964694 * 2 ^ 59
def prefixEnd_2964694 : Nat := 4983230072969 + 3 ^ 40 * 2964694 * 2
def baseEnd_2964694 : Nat := 507437671833576284930209

theorem tailTrace_2964694 : CollatzResearch.WordTrace tailWord_2964694 prefixEnd_2964694 507437671833576284930209 := by
  unfold tailWord_2964694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758204595089215141835321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72087515680951628179576757 6758204595089215141835321)
  ·
    refine ⟨5068653446316911356376491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6758204595089215141835321 5068653446316911356376491)
    ·
      refine ⟨7602980169475367034564737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5068653446316911356376491 7602980169475367034564737)
      ·
        refine ⟨5702235127106525275923553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7602980169475367034564737 5702235127106525275923553)
        ·
          refine ⟨4276676345329893956942665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5702235127106525275923553 4276676345329893956942665)
          ·
            refine ⟨3207507258997420467706999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4276676345329893956942665 3207507258997420467706999)
            ·
              refine ⟨4811260888496130701560499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207507258997420467706999 4811260888496130701560499)
              ·
                refine ⟨7216891332744196052340749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811260888496130701560499 7216891332744196052340749)
                ·
                  refine ⟨2706334249779073519627781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7216891332744196052340749 2706334249779073519627781)
                  ·
                    refine ⟨507437671833576284930209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706334249779073519627781 507437671833576284930209)
                    ·
                      rfl

theorem cell23_2964694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2964694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964694 prefixEnd_2964694 := by exact prefixLift 2964694
  have htrace : WordTrace (prefixWord ++ tailWord_2964694) baseStart_2964694 baseEnd_2964694 := by
    simpa [prefixWord, tailWord_2964694, baseEnd_2964694] using wordTrace_append hprefix tailTrace_2964694
  have hstable : (prefixWord ++ tailWord_2964694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964694).length < 2 ^ (prefixWord ++ tailWord_2964694).sum := by decide
  have hdescent : baseEnd_2964694 < baseStart_2964694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964723 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 4]
def baseStart_2964723 : Nat := 118140960795 + 2964723 * 2 ^ 59
def prefixEnd_2964723 : Nat := 4983230072969 + 3 ^ 40 * 2964723 * 2
def baseEnd_2964723 : Nat := 1522327906439709241327993

theorem tailTrace_2964723 : CollatzResearch.WordTrace tailWord_2964723 prefixEnd_2964723 1522327906439709241327993 := by
  unfold tailWord_2964723
  simp only [CollatzResearch.WordTrace]
  refine ⟨108132331238322380222170823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72088220825548253481447215 108132331238322380222170823)
  ·
    refine ⟨162198496857483570333256235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108132331238322380222170823 162198496857483570333256235)
    ·
      refine ⟨243297745286225355499884353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162198496857483570333256235 243297745286225355499884353)
      ·
        refine ⟨182473308964669016624913265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243297745286225355499884353 182473308964669016624913265)
        ·
          refine ⟨136854981723501762468684949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182473308964669016624913265 136854981723501762468684949)
          ·
            refine ⟨6415077268289145115719607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136854981723501762468684949 6415077268289145115719607)
            ·
              refine ⟨9622615902433717673579411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415077268289145115719607 9622615902433717673579411)
              ·
                refine ⟨14433923853650576510369117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9622615902433717673579411 14433923853650576510369117)
                ·
                  refine ⟨5412721445118966191388419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14433923853650576510369117 5412721445118966191388419)
                  ·
                    refine ⟨8119082167678449287082629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5412721445118966191388419 8119082167678449287082629)
                    ·
                      refine ⟨1522327906439709241327993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8119082167678449287082629 1522327906439709241327993)
                      ·
                        rfl

theorem cell23_2964723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_2964723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964723 prefixEnd_2964723 := by exact prefixLift 2964723
  have htrace : WordTrace (prefixWord ++ tailWord_2964723) baseStart_2964723 baseEnd_2964723 := by
    simpa [prefixWord, tailWord_2964723, baseEnd_2964723] using wordTrace_append hprefix tailTrace_2964723
  have hstable : (prefixWord ++ tailWord_2964723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964723).length < 2 ^ (prefixWord ++ tailWord_2964723).sum := by decide
  have hdescent : baseEnd_2964723 < baseStart_2964723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964750 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_2964750 : Nat := 118140960795 + 2964750 * 2 ^ 59
def prefixEnd_2964750 : Nat := 4983230072969 + 3 ^ 40 * 2964750 * 2
def baseEnd_2964750 : Nat := 507447256805793545230123

theorem tailTrace_2964750 : CollatzResearch.WordTrace tailWord_2964750 prefixEnd_2964750 507447256805793545230123 := by
  unfold tailWord_2964750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13516664501153070479175463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72088877339483042555602469 13516664501153070479175463)
  ·
    refine ⟨20274996751729605718763195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13516664501153070479175463 20274996751729605718763195)
    ·
      refine ⟨30412495127594408578144793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20274996751729605718763195 30412495127594408578144793)
      ·
        refine ⟨22809371345695806433608595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30412495127594408578144793 22809371345695806433608595)
        ·
          refine ⟨34214057018543709650412893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22809371345695806433608595 34214057018543709650412893)
          ·
            refine ⟨12830271381953891118904835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34214057018543709650412893 12830271381953891118904835)
            ·
              refine ⟨19245407072930836678357253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12830271381953891118904835 19245407072930836678357253)
              ·
                refine ⟨3608513826174531877191985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19245407072930836678357253 3608513826174531877191985)
                ·
                  refine ⟨2706385369630898907893989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608513826174531877191985 2706385369630898907893989)
                  ·
                    refine ⟨507447256805793545230123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706385369630898907893989 507447256805793545230123)
                    ·
                      rfl

theorem cell23_2964750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_2964750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964750 prefixEnd_2964750 := by exact prefixLift 2964750
  have htrace : WordTrace (prefixWord ++ tailWord_2964750) baseStart_2964750 baseEnd_2964750 := by
    simpa [prefixWord, tailWord_2964750, baseEnd_2964750] using wordTrace_append hprefix tailTrace_2964750
  have hstable : (prefixWord ++ tailWord_2964750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964750).length < 2 ^ (prefixWord ++ tailWord_2964750).sum := by decide
  have hdescent : baseEnd_2964750 < baseStart_2964750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964807 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_2964807 : Nat := 118140960795 + 2964807 * 2 ^ 59
def prefixEnd_2964807 : Nat := 4983230072969 + 3 ^ 40 * 2964807 * 2
def baseEnd_2964807 : Nat := 1522371038814686912677607

theorem tailTrace_2964807 : CollatzResearch.WordTrace tailWord_2964807 prefixEnd_2964807 1522371038814686912677607 := by
  unfold tailWord_2964807
  simp only [CollatzResearch.WordTrace]
  refine ⟨108135394970018062568228675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72090263313345375045485783 108135394970018062568228675)
  ·
    refine ⟨162203092455027093852343013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108135394970018062568228675 162203092455027093852343013)
    ·
      refine ⟨30413079835317580097314315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162203092455027093852343013 30413079835317580097314315)
      ·
        refine ⟨45619619752976370145971473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30413079835317580097314315 45619619752976370145971473)
        ·
          refine ⟨34214714814732277609478605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45619619752976370145971473 34214714814732277609478605)
          ·
            refine ⟨12830518055524604103554477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34214714814732277609478605 12830518055524604103554477)
            ·
              refine ⟨4811444270821726538832929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12830518055524604103554477 4811444270821726538832929)
              ·
                refine ⟨3608583203116294904124697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811444270821726538832929 3608583203116294904124697)
                ·
                  refine ⟨2706437402337221178093523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608583203116294904124697 2706437402337221178093523)
                  ·
                    refine ⟨4059656103505831767140285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706437402337221178093523 4059656103505831767140285)
                    ·
                      refine ⟨1522371038814686912677607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059656103505831767140285 1522371038814686912677607)
                      ·
                        rfl

theorem cell23_2964807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_2964807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964807 prefixEnd_2964807 := by exact prefixLift 2964807
  have htrace : WordTrace (prefixWord ++ tailWord_2964807) baseStart_2964807 baseEnd_2964807 := by
    simpa [prefixWord, tailWord_2964807, baseEnd_2964807] using wordTrace_append hprefix tailTrace_2964807
  have hstable : (prefixWord ++ tailWord_2964807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964807).length < 2 ^ (prefixWord ++ tailWord_2964807).sum := by decide
  have hdescent : baseEnd_2964807 < baseStart_2964807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964823 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 2, 6]
def baseStart_2964823 : Nat := 118140960795 + 2964823 * 2 ^ 59
def prefixEnd_2964823 : Nat := 4983230072969 + 3 ^ 40 * 2964823 * 2
def baseEnd_2964823 : Nat := 507459751501719616692511

theorem tailTrace_2964823 : CollatzResearch.WordTrace tailWord_2964823 prefixEnd_2964823 507459751501719616692511 := by
  unfold tailWord_2964823
  simp only [CollatzResearch.WordTrace]
  refine ⟨108135978537960097300811123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72090652358640064867207415 108135978537960097300811123)
  ·
    refine ⟨162203967806940145951216685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108135978537960097300811123 162203967806940145951216685)
    ·
      refine ⟨60826487927602554731706257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162203967806940145951216685 60826487927602554731706257)
      ·
        refine ⟨45619865945701916048779693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60826487927602554731706257 45619865945701916048779693)
        ·
          refine ⟨17107449729638218518292385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45619865945701916048779693 17107449729638218518292385)
          ·
            refine ⟨12830587297228663888719289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17107449729638218518292385 12830587297228663888719289)
            ·
              refine ⟨9622940472921497916539467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12830587297228663888719289 9622940472921497916539467)
              ·
                refine ⟨14434410709382246874809201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9622940472921497916539467 14434410709382246874809201)
                ·
                  refine ⟨10825808032036685156106901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14434410709382246874809201 10825808032036685156106901)
                  ·
                    refine ⟨507459751501719616692511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10825808032036685156106901 507459751501719616692511)
                    ·
                      rfl

theorem cell23_2964823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_2964823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964823 prefixEnd_2964823 := by exact prefixLift 2964823
  have htrace : WordTrace (prefixWord ++ tailWord_2964823) baseStart_2964823 baseEnd_2964823 := by
    simpa [prefixWord, tailWord_2964823, baseEnd_2964823] using wordTrace_append hprefix tailTrace_2964823
  have hstable : (prefixWord ++ tailWord_2964823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964823).length < 2 ^ (prefixWord ++ tailWord_2964823).sum := by decide
  have hdescent : baseEnd_2964823 < baseStart_2964823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964833 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2964833 : Nat := 118140960795 + 2964833 * 2 ^ 59
def prefixEnd_2964833 : Nat := 4983230072969 + 3 ^ 40 * 2964833 * 2
def baseEnd_2964833 : Nat := 1522384389311703810952487

theorem tailTrace_2964833 : CollatzResearch.WordTrace tailWord_2964833 prefixEnd_2964833 1522384389311703810952487 := by
  unfold tailWord_2964833
  simp only [CollatzResearch.WordTrace]
  refine ⟨108136343267923869008675153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72090895511949246005783435 108136343267923869008675153)
  ·
    refine ⟨81102257450942901756506365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108136343267923869008675153 81102257450942901756506365)
    ·
      refine ⟨30413346544103588158689887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81102257450942901756506365 30413346544103588158689887)
      ·
        refine ⟨45620019816155382238034831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30413346544103588158689887 45620019816155382238034831)
        ·
          refine ⟨68430029724233073357052247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45620019816155382238034831 68430029724233073357052247)
          ·
            refine ⟨102645044586349610035578371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68430029724233073357052247 102645044586349610035578371)
            ·
              refine ⟨153967566879524415053367557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102645044586349610035578371 153967566879524415053367557)
              ·
                refine ⟨28868918789910827822506417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153967566879524415053367557 28868918789910827822506417)
                ·
                  refine ⟨21651689092433120866879813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28868918789910827822506417 21651689092433120866879813)
                  ·
                    refine ⟨4059691704831210162539965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21651689092433120866879813 4059691704831210162539965)
                    ·
                      refine ⟨1522384389311703810952487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059691704831210162539965 1522384389311703810952487)
                      ·
                        rfl

theorem cell23_2964833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2964833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964833 prefixEnd_2964833 := by exact prefixLift 2964833
  have htrace : WordTrace (prefixWord ++ tailWord_2964833) baseStart_2964833 baseEnd_2964833 := by
    simpa [prefixWord, tailWord_2964833, baseEnd_2964833] using wordTrace_append hprefix tailTrace_2964833
  have hstable : (prefixWord ++ tailWord_2964833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964833).length < 2 ^ (prefixWord ++ tailWord_2964833).sum := by decide
  have hdescent : baseEnd_2964833 < baseStart_2964833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964834 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_2964834 : Nat := 118140960795 + 2964834 * 2 ^ 59
def prefixEnd_2964834 : Nat := 4983230072969 + 3 ^ 40 * 2964834 * 2
def baseEnd_2964834 : Nat := 1522384902792358307039983

theorem tailTrace_2964834 : CollatzResearch.WordTrace tailWord_2964834 prefixEnd_2964834 1522384902792358307039983 := by
  unfold tailWord_2964834
  simp only [CollatzResearch.WordTrace]
  refine ⟨27034094935230061544865389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72090919827280164119641037 27034094935230061544865389)
  ·
    refine ⟨10137785600711273079324521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27034094935230061544865389 10137785600711273079324521)
    ·
      refine ⟨7603339200533454809493391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10137785600711273079324521 7603339200533454809493391)
      ·
        refine ⟨11405008800800182214240087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7603339200533454809493391 11405008800800182214240087)
        ·
          refine ⟨17107513201200273321360131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405008800800182214240087 17107513201200273321360131)
          ·
            refine ⟨25661269801800409982040197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17107513201200273321360131 25661269801800409982040197)
            ·
              refine ⟨4811488087837576871632537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25661269801800409982040197 4811488087837576871632537)
              ·
                refine ⟨3608616065878182653724403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811488087837576871632537 3608616065878182653724403)
                ·
                  refine ⟨5412924098817273980586605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608616065878182653724403 5412924098817273980586605)
                  ·
                    refine ⟨2029846537056477742719977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5412924098817273980586605 2029846537056477742719977)
                    ·
                      refine ⟨1522384902792358307039983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2029846537056477742719977 1522384902792358307039983)
                      ·
                        rfl

theorem cell23_2964834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_2964834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964834 prefixEnd_2964834 := by exact prefixLift 2964834
  have htrace : WordTrace (prefixWord ++ tailWord_2964834) baseStart_2964834 baseEnd_2964834 := by
    simpa [prefixWord, tailWord_2964834, baseEnd_2964834] using wordTrace_append hprefix tailTrace_2964834
  have hstable : (prefixWord ++ tailWord_2964834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964834).length < 2 ^ (prefixWord ++ tailWord_2964834).sum := by decide
  have hdescent : baseEnd_2964834 < baseStart_2964834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964920 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_2964920 : Nat := 118140960795 + 2964920 * 2 ^ 59
def prefixEnd_2964920 : Nat := 4983230072969 + 3 ^ 40 * 2964920 * 2
def baseEnd_2964920 : Nat := 1522429062128644970564587

theorem tailTrace_2964920 : CollatzResearch.WordTrace tailWord_2964920 prefixEnd_2964920 1522429062128644970564587 := by
  unfold tailWord_2964920
  simp only [CollatzResearch.WordTrace]
  refine ⟨54069758209304341433546107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72093010945739121911394809 54069758209304341433546107)
  ·
    refine ⟨81104637313956512150319161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54069758209304341433546107 81104637313956512150319161)
    ·
      refine ⟨60828477985467384112739371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81104637313956512150319161 60828477985467384112739371)
      ·
        refine ⟨91242716978201076169109057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60828477985467384112739371 91242716978201076169109057)
        ·
          refine ⟨68432037733650807126831793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91242716978201076169109057 68432037733650807126831793)
          ·
            refine ⟨51324028300238105345123845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68432037733650807126831793 51324028300238105345123845)
            ·
              refine ⟨9623255306294644752210721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51324028300238105345123845 9623255306294644752210721)
              ·
                refine ⟨7217441479720983564158041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9623255306294644752210721 7217441479720983564158041)
                ·
                  refine ⟨5413081109790737673118531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7217441479720983564158041 5413081109790737673118531)
                  ·
                    refine ⟨8119621664686106509677797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413081109790737673118531 8119621664686106509677797)
                    ·
                      refine ⟨1522429062128644970564587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8119621664686106509677797 1522429062128644970564587)
                      ·
                        rfl

theorem cell23_2964920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_2964920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964920 prefixEnd_2964920 := by exact prefixLift 2964920
  have htrace : WordTrace (prefixWord ++ tailWord_2964920) baseStart_2964920 baseEnd_2964920 := by
    simpa [prefixWord, tailWord_2964920, baseEnd_2964920] using wordTrace_append hprefix tailTrace_2964920
  have hstable : (prefixWord ++ tailWord_2964920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964920).length < 2 ^ (prefixWord ++ tailWord_2964920).sum := by decide
  have hdescent : baseEnd_2964920 < baseStart_2964920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964921 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 5]
def baseStart_2964921 : Nat := 118140960795 + 2964921 * 2 ^ 59
def prefixEnd_2964921 : Nat := 4983230072969 + 3 ^ 40 * 2964921 * 2
def baseEnd_2964921 : Nat := 169158841734366607405787

theorem tailTrace_2964921 : CollatzResearch.WordTrace tailWord_2964921 prefixEnd_2964921 169158841734366607405787 := by
  unfold tailWord_2964921
  simp only [CollatzResearch.WordTrace]
  refine ⟨108139552891605060037878617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72093035261070040025252411 108139552891605060037878617)
  ·
    refine ⟨81104664668703795028408963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108139552891605060037878617 81104664668703795028408963)
    ·
      refine ⟨121656997003055692542613445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81104664668703795028408963 121656997003055692542613445)
      ·
        refine ⟨22810686938072942351740021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121656997003055692542613445 22810686938072942351740021)
        ·
          refine ⟨2138501900444338345475627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22810686938072942351740021 2138501900444338345475627)
          ·
            refine ⟨3207752850666507518213441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138501900444338345475627 3207752850666507518213441)
            ·
              refine ⟨2405814637999880638660081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3207752850666507518213441 2405814637999880638660081)
              ·
                refine ⟨1804360978499910478995061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405814637999880638660081 1804360978499910478995061)
                ·
                  refine ⟨169158841734366607405787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1804360978499910478995061 169158841734366607405787)
                  ·
                    rfl

theorem cell23_2964921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 5].length) (baseStart_2964921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964921 prefixEnd_2964921 := by exact prefixLift 2964921
  have htrace : WordTrace (prefixWord ++ tailWord_2964921) baseStart_2964921 baseEnd_2964921 := by
    simpa [prefixWord, tailWord_2964921, baseEnd_2964921] using wordTrace_append hprefix tailTrace_2964921
  have hstable : (prefixWord ++ tailWord_2964921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964921).length < 2 ^ (prefixWord ++ tailWord_2964921).sum := by decide
  have hdescent : baseEnd_2964921 < baseStart_2964921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964957 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2964957 : Nat := 118140960795 + 2964957 * 2 ^ 59
def prefixEnd_2964957 : Nat := 4983230072969 + 3 ^ 40 * 2964957 * 2
def baseEnd_2964957 : Nat := 1522448060912861325801917

theorem tailTrace_2964957 : CollatzResearch.WordTrace tailWord_2964957 prefixEnd_2964957 1522448060912861325801917 := by
  unfold tailWord_2964957
  simp only [CollatzResearch.WordTrace]
  refine ⟨108140865919474638186189125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72093910612983092124126083 108140865919474638186189125)
  ·
    refine ⟨20276412359901494659910461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108140865919474638186189125 20276412359901494659910461)
    ·
      refine ⟨7603654634963060497466423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20276412359901494659910461 7603654634963060497466423)
      ·
        refine ⟨11405481952444590746199635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7603654634963060497466423 11405481952444590746199635)
        ·
          refine ⟨17108222928666886119299453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405481952444590746199635 17108222928666886119299453)
          ·
            refine ⟨6415583598250082294737295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17108222928666886119299453 6415583598250082294737295)
            ·
              refine ⟨9623375397375123442105943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415583598250082294737295 9623375397375123442105943)
              ·
                refine ⟨14435063096062685163158915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623375397375123442105943 14435063096062685163158915)
                ·
                  refine ⟨21652594644094027744738373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14435063096062685163158915 21652594644094027744738373)
                  ·
                    refine ⟨4059861495767630202138445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21652594644094027744738373 4059861495767630202138445)
                    ·
                      refine ⟨1522448060912861325801917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4059861495767630202138445 1522448060912861325801917)
                      ·
                        rfl

theorem cell23_2964957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2964957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964957 prefixEnd_2964957 := by exact prefixLift 2964957
  have htrace : WordTrace (prefixWord ++ tailWord_2964957) baseStart_2964957 baseEnd_2964957 := by
    simpa [prefixWord, tailWord_2964957, baseEnd_2964957] using wordTrace_append hprefix tailTrace_2964957
  have hstable : (prefixWord ++ tailWord_2964957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964957).length < 2 ^ (prefixWord ++ tailWord_2964957).sum := by decide
  have hdescent : baseEnd_2964957 < baseStart_2964957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964977 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 6]
def baseStart_2964977 : Nat := 118140960795 + 2964977 * 2 ^ 59
def prefixEnd_2964977 : Nat := 4983230072969 + 3 ^ 40 * 2964977 * 2
def baseEnd_2964977 : Nat := 169162036725105694172425

theorem tailTrace_2964977 : CollatzResearch.WordTrace tailWord_2964977 prefixEnd_2964977 169162036725105694172425 := by
  unfold tailWord_2964977
  simp only [CollatzResearch.WordTrace]
  refine ⟨108141595379402181601917185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72094396919601454401278123 108141595379402181601917185)
  ·
    refine ⟨81106196534551636201437889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108141595379402181601917185 81106196534551636201437889)
    ·
      refine ⟨60829647400913727151078417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81106196534551636201437889 60829647400913727151078417)
      ·
        refine ⟨45622235550685295363308813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60829647400913727151078417 45622235550685295363308813)
        ·
          refine ⟨17108338331506985761240805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45622235550685295363308813 17108338331506985761240805)
          ·
            refine ⟨3207813437157559830232651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17108338331506985761240805 3207813437157559830232651)
            ·
              refine ⟨4811720155736339745348977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207813437157559830232651 4811720155736339745348977)
              ·
                refine ⟨3608790116802254809011733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811720155736339745348977 3608790116802254809011733)
                ·
                  refine ⟨169162036725105694172425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3608790116802254809011733 169162036725105694172425)
                  ·
                    rfl

theorem cell23_2964977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 6].length) (baseStart_2964977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964977 prefixEnd_2964977 := by exact prefixLift 2964977
  have htrace : WordTrace (prefixWord ++ tailWord_2964977) baseStart_2964977 baseEnd_2964977 := by
    simpa [prefixWord, tailWord_2964977, baseEnd_2964977] using wordTrace_append hprefix tailTrace_2964977
  have hstable : (prefixWord ++ tailWord_2964977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964977).length < 2 ^ (prefixWord ++ tailWord_2964977).sum := by decide
  have hdescent : baseEnd_2964977 < baseStart_2964977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964981 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2964981 : Nat := 118140960795 + 2964981 * 2 ^ 59
def prefixEnd_2964981 : Nat := 4983230072969 + 3 ^ 40 * 2964981 * 2
def baseEnd_2964981 : Nat := 507486794816189743967269

theorem tailTrace_2964981 : CollatzResearch.WordTrace tailWord_2964981 prefixEnd_2964981 507486794816189743967269 := by
  unfold tailWord_2964981
  simp only [CollatzResearch.WordTrace]
  refine ⟨108141741271387690285062797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72094494180925126856708531 108141741271387690285062797)
  ·
    refine ⟨40553152976770383856898549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108141741271387690285062797 40553152976770383856898549)
    ·
      refine ⟨3801858091572223486584239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40553152976770383856898549 3801858091572223486584239)
      ·
        refine ⟨5702787137358335229876359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801858091572223486584239 5702787137358335229876359)
        ·
          refine ⟨8554180706037502844814539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702787137358335229876359 8554180706037502844814539)
          ·
            refine ⟨12831271059056254267221809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8554180706037502844814539 12831271059056254267221809)
            ·
              refine ⟨9623453294292190700416357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12831271059056254267221809 9623453294292190700416357)
              ·
                refine ⟨1804397492679785756328067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9623453294292190700416357 1804397492679785756328067)
                ·
                  refine ⟨2706596239019678634492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804397492679785756328067 2706596239019678634492101)
                  ·
                    refine ⟨507486794816189743967269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706596239019678634492101 507486794816189743967269)
                    ·
                      rfl

theorem cell23_2964981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2964981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964981 prefixEnd_2964981 := by exact prefixLift 2964981
  have htrace : WordTrace (prefixWord ++ tailWord_2964981) baseStart_2964981 baseEnd_2964981 := by
    simpa [prefixWord, tailWord_2964981, baseEnd_2964981] using wordTrace_append hprefix tailTrace_2964981
  have hstable : (prefixWord ++ tailWord_2964981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964981).length < 2 ^ (prefixWord ++ tailWord_2964981).sum := by decide
  have hdescent : baseEnd_2964981 < baseStart_2964981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964983 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_2964983 : Nat := 118140960795 + 2964983 * 2 ^ 59
def prefixEnd_2964983 : Nat := 4983230072969 + 3 ^ 40 * 2964983 * 2
def baseEnd_2964983 : Nat := 1522461411409878224076797

theorem tailTrace_2964983 : CollatzResearch.WordTrace tailWord_2964983 prefixEnd_2964983 1522461411409878224076797 := by
  unfold tailWord_2964983
  simp only [CollatzResearch.WordTrace]
  refine ⟨108141814217380444626635603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72094542811586963084423735 108141814217380444626635603)
  ·
    refine ⟨162212721326070666939953405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108141814217380444626635603 162212721326070666939953405)
    ·
      refine ⟨60829770497276500102482527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162212721326070666939953405 60829770497276500102482527)
      ·
        refine ⟨91244655745914750153723791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60829770497276500102482527 91244655745914750153723791)
        ·
          refine ⟨136866983618872125230585687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91244655745914750153723791 136866983618872125230585687)
          ·
            refine ⟨205300475428308187845878531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136866983618872125230585687 205300475428308187845878531)
            ·
              refine ⟨307950713142462281768817797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205300475428308187845878531 307950713142462281768817797)
              ·
                refine ⟨57740758714211677831653337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307950713142462281768817797 57740758714211677831653337)
                ·
                  refine ⟨43305569035658758373740003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57740758714211677831653337 43305569035658758373740003)
                  ·
                    refine ⟨64958353553488137560610005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43305569035658758373740003 64958353553488137560610005)
                    ·
                      refine ⟨1522461411409878224076797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64958353553488137560610005 1522461411409878224076797)
                      ·
                        rfl

theorem cell23_2964983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_2964983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2964983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2964983 prefixEnd_2964983 := by exact prefixLift 2964983
  have htrace : WordTrace (prefixWord ++ tailWord_2964983) baseStart_2964983 baseEnd_2964983 := by
    simpa [prefixWord, tailWord_2964983, baseEnd_2964983] using wordTrace_append hprefix tailTrace_2964983
  have hstable : (prefixWord ++ tailWord_2964983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964983).length < 2 ^ (prefixWord ++ tailWord_2964983).sum := by decide
  have hdescent : baseEnd_2964983 < baseStart_2964983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965020 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2965020 : Nat := 118140960795 + 2965020 * 2 ^ 59
def prefixEnd_2965020 : Nat := 4983230072969 + 3 ^ 40 * 2965020 * 2
def baseEnd_2965020 : Nat := 507493470064698193104709

theorem tailTrace_2965020 : CollatzResearch.WordTrace tailWord_2965020 prefixEnd_2965020 507493470064698193104709 := by
  unfold tailWord_2965020
  simp only [CollatzResearch.WordTrace]
  refine ⟨54071581859123199972866257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72095442478830933297155009 54071581859123199972866257)
  ·
    refine ⟨40553686394342399979649693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54071581859123199972866257 40553686394342399979649693)
    ·
      refine ⟨15207632397878399992368635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40553686394342399979649693 15207632397878399992368635)
      ·
        refine ⟨22811448596817599988552953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15207632397878399992368635 22811448596817599988552953)
        ·
          refine ⟨17108586447613199991414715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22811448596817599988552953 17108586447613199991414715)
          ·
            refine ⟨25662879671419799987122073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108586447613199991414715 25662879671419799987122073)
            ·
              refine ⟨19247159753564849990341555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25662879671419799987122073 19247159753564849990341555)
              ·
                refine ⟨28870739630347274985512333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19247159753564849990341555 28870739630347274985512333)
                ·
                  refine ⟨10826527361380228119567125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28870739630347274985512333 10826527361380228119567125)
                  ·
                    refine ⟨507493470064698193104709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10826527361380228119567125 507493470064698193104709)
                    ·
                      rfl

theorem cell23_2965020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2965020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965020 prefixEnd_2965020 := by exact prefixLift 2965020
  have htrace : WordTrace (prefixWord ++ tailWord_2965020) baseStart_2965020 baseEnd_2965020 := by
    simpa [prefixWord, tailWord_2965020, baseEnd_2965020] using wordTrace_append hprefix tailTrace_2965020
  have hstable : (prefixWord ++ tailWord_2965020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965020).length < 2 ^ (prefixWord ++ tailWord_2965020).sum := by decide
  have hdescent : baseEnd_2965020 < baseStart_2965020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965050 : List Nat := [3, 1, 1, 1, 3, 2, 4, 8]
def baseStart_2965050 : Nat := 118140960795 + 2965050 * 2 ^ 59
def prefixEnd_2965050 : Nat := 4983230072969 + 3 ^ 40 * 2965050 * 2
def baseEnd_2965050 : Nat := 56388733874582572664407

theorem tailTrace_2965050 : CollatzResearch.WordTrace tailWord_2965050 prefixEnd_2965050 56388733874582572664407 := by
  unfold tailWord_2965050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27036064477034428767331151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72096171938758476712883069 27036064477034428767331151)
  ·
    refine ⟨40554096715551643150996727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27036064477034428767331151 40554096715551643150996727)
    ·
      refine ⟨60831145073327464726495091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40554096715551643150996727 60831145073327464726495091)
      ·
        refine ⟨91246717609991197089742637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60831145073327464726495091 91246717609991197089742637)
        ·
          refine ⟨34217519103746698908653489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91246717609991197089742637 34217519103746698908653489)
          ·
            refine ⟨25663139327810024181490117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34217519103746698908653489 25663139327810024181490117)
            ·
              refine ⟨4811838623964379534029397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25663139327810024181490117 4811838623964379534029397)
              ·
                refine ⟨56388733874582572664407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4811838623964379534029397 56388733874582572664407)
                ·
                  rfl

theorem cell23_2965050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_2965050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965050 prefixEnd_2965050 := by exact prefixLift 2965050
  have htrace : WordTrace (prefixWord ++ tailWord_2965050) baseStart_2965050 baseEnd_2965050 := by
    simpa [prefixWord, tailWord_2965050, baseEnd_2965050] using wordTrace_append hprefix tailTrace_2965050
  have hstable : (prefixWord ++ tailWord_2965050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965050).length < 2 ^ (prefixWord ++ tailWord_2965050).sum := by decide
  have hdescent : baseEnd_2965050 < baseStart_2965050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965057 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2965057 : Nat := 118140960795 + 2965057 * 2 ^ 59
def prefixEnd_2965057 : Nat := 4983230072969 + 3 ^ 40 * 2965057 * 2
def baseEnd_2965057 : Nat := 1522499408978310934551457

theorem tailTrace_2965057 : CollatzResearch.WordTrace tailWord_2965057 prefixEnd_2965057 1522499408978310934551457 := by
  unfold tailWord_2965057
  simp only [CollatzResearch.WordTrace]
  refine ⟨108144513219112355264829425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72096342146074903509886283 108144513219112355264829425)
  ·
    refine ⟨81108384914334266448622069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108144513219112355264829425 81108384914334266448622069)
    ·
      refine ⟨7603911085718837479558319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81108384914334266448622069 7603911085718837479558319)
      ·
        refine ⟨11405866628578256219337479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7603911085718837479558319 11405866628578256219337479)
        ·
          refine ⟨17108799942867384329006219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405866628578256219337479 17108799942867384329006219)
          ·
            refine ⟨25663199914301076493509329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108799942867384329006219 25663199914301076493509329)
            ·
              refine ⟨19247399935725807370131997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25663199914301076493509329 19247399935725807370131997)
              ·
                refine ⟨7217774975897177763799499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19247399935725807370131997 7217774975897177763799499)
                ·
                  refine ⟨10826662463845766645699249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7217774975897177763799499 10826662463845766645699249)
                  ·
                    refine ⟨8119996847884324984274437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10826662463845766645699249 8119996847884324984274437)
                    ·
                      refine ⟨1522499408978310934551457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8119996847884324984274437 1522499408978310934551457)
                      ·
                        rfl

theorem cell23_2965057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2965057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965057 prefixEnd_2965057 := by exact prefixLift 2965057
  have htrace : WordTrace (prefixWord ++ tailWord_2965057) baseStart_2965057 baseEnd_2965057 := by
    simpa [prefixWord, tailWord_2965057, baseEnd_2965057] using wordTrace_append hprefix tailTrace_2965057
  have hstable : (prefixWord ++ tailWord_2965057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965057).length < 2 ^ (prefixWord ++ tailWord_2965057).sum := by decide
  have hdescent : baseEnd_2965057 < baseStart_2965057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965104 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 3, 3, 2]
def baseStart_2965104 : Nat := 118140960795 + 2965104 * 2 ^ 59
def prefixEnd_2965104 : Nat := 4983230072969 + 3 ^ 40 * 2965104 * 2
def baseEnd_2965104 : Nat := 1522523542569072250663741

theorem tailTrace_2965104 : CollatzResearch.WordTrace tailWord_2965104 prefixEnd_2965104 1522523542569072250663741 := by
  unfold tailWord_2965104
  simp only [CollatzResearch.WordTrace]
  refine ⟨54073113724971041145895183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72097484966628054861193577 54073113724971041145895183)
  ·
    refine ⟨81109670587456561718842775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54073113724971041145895183 81109670587456561718842775)
    ·
      refine ⟨121664505881184842578264163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81109670587456561718842775 121664505881184842578264163)
      ·
        refine ⟨182496758821777263867396245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121664505881184842578264163 182496758821777263867396245)
        ·
          refine ⟨8554535569770809243784199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 182496758821777263867396245 8554535569770809243784199)
          ·
            refine ⟨12831803354656213865676299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8554535569770809243784199 12831803354656213865676299)
            ·
              refine ⟨19247705031984320798514449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12831803354656213865676299 19247705031984320798514449)
              ·
                refine ⟨14435778773988240598885837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19247705031984320798514449 14435778773988240598885837)
                ·
                  refine ⟨5413417040245590224582189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14435778773988240598885837 5413417040245590224582189)
                  ·
                    refine ⟨2030031390092096334218321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5413417040245590224582189 2030031390092096334218321)
                    ·
                      refine ⟨1522523542569072250663741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030031390092096334218321 1522523542569072250663741)
                      ·
                        rfl

theorem cell23_2965104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 3, 2].length) (baseStart_2965104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965104 prefixEnd_2965104 := by exact prefixLift 2965104
  have htrace : WordTrace (prefixWord ++ tailWord_2965104) baseStart_2965104 baseEnd_2965104 := by
    simpa [prefixWord, tailWord_2965104, baseEnd_2965104] using wordTrace_append hprefix tailTrace_2965104
  have hstable : (prefixWord ++ tailWord_2965104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965104).length < 2 ^ (prefixWord ++ tailWord_2965104).sum := by decide
  have hdescent : baseEnd_2965104 < baseStart_2965104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965138 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2965138 : Nat := 118140960795 + 2965138 * 2 ^ 59
def prefixEnd_2965138 : Nat := 4983230072969 + 3 ^ 40 * 2965138 * 2
def baseEnd_2965138 : Nat := 1522541000911325117638585

theorem tailTrace_2965138 : CollatzResearch.WordTrace tailWord_2965138 prefixEnd_2965138 1522541000911325117638585 := by
  unfold tailWord_2965138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27036866882954726524632017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72098311687879270732352045 27036866882954726524632017)
  ·
    refine ⟨20277650162216044893474013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27036866882954726524632017 20277650162216044893474013)
    ·
      refine ⟨7604118810831016835052755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20277650162216044893474013 7604118810831016835052755)
      ·
        refine ⟨11406178216246525252579133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7604118810831016835052755 11406178216246525252579133)
        ·
          refine ⟨4277316831092446969717175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11406178216246525252579133 4277316831092446969717175)
          ·
            refine ⟨6415975246638670454575763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277316831092446969717175 6415975246638670454575763)
            ·
              refine ⟨9623962869958005681863645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415975246638670454575763 9623962869958005681863645)
              ·
                refine ⟨3608986076234252130698867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9623962869958005681863645 3608986076234252130698867)
                ·
                  refine ⟨5413479114351378196048301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608986076234252130698867 5413479114351378196048301)
                  ·
                    refine ⟨2030054667881766823518113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5413479114351378196048301 2030054667881766823518113)
                    ·
                      refine ⟨1522541000911325117638585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030054667881766823518113 1522541000911325117638585)
                      ·
                        rfl

theorem cell23_2965138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2965138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965138 prefixEnd_2965138 := by exact prefixLift 2965138
  have htrace : WordTrace (prefixWord ++ tailWord_2965138) baseStart_2965138 baseEnd_2965138 := by
    simpa [prefixWord, tailWord_2965138, baseEnd_2965138] using wordTrace_append hprefix tailTrace_2965138
  have hstable : (prefixWord ++ tailWord_2965138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965138).length < 2 ^ (prefixWord ++ tailWord_2965138).sum := by decide
  have hdescent : baseEnd_2965138 < baseStart_2965138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965167 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_2965167 : Nat := 118140960795 + 2965167 * 2 ^ 59
def prefixEnd_2965167 : Nat := 4983230072969 + 3 ^ 40 * 2965167 * 2
def baseEnd_2965167 : Nat := 1522555891850305504175951

theorem tailTrace_2965167 : CollatzResearch.WordTrace tailWord_2965167 prefixEnd_2965167 1522555891850305504175951 := by
  unfold tailWord_2965167
  simp only [CollatzResearch.WordTrace]
  refine ⟨108148525248713844051333755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72099016832475896034222503 108148525248713844051333755)
  ·
    refine ⟨162222787873070766077000633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108148525248713844051333755 162222787873070766077000633)
    ·
      refine ⟨121667090904803074557750475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162222787873070766077000633 121667090904803074557750475)
      ·
        refine ⟨182500636357204611836625713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121667090904803074557750475 182500636357204611836625713)
        ·
          refine ⟨136875477267903458877469285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182500636357204611836625713 136875477267903458877469285)
          ·
            refine ⟨25664151987731898539525491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136875477267903458877469285 25664151987731898539525491)
            ·
              refine ⟨38496227981597847809288237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25664151987731898539525491 38496227981597847809288237)
              ·
                refine ⟨14436085493099192928483089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38496227981597847809288237 14436085493099192928483089)
                ·
                  refine ⟨10827064119824394696362317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14436085493099192928483089 10827064119824394696362317)
                  ·
                    refine ⟨4060149044934148011135869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10827064119824394696362317 4060149044934148011135869)
                    ·
                      refine ⟨1522555891850305504175951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060149044934148011135869 1522555891850305504175951)
                      ·
                        rfl

theorem cell23_2965167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_2965167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965167 prefixEnd_2965167 := by exact prefixLift 2965167
  have htrace : WordTrace (prefixWord ++ tailWord_2965167) baseStart_2965167 baseEnd_2965167 := by
    simpa [prefixWord, tailWord_2965167, baseEnd_2965167] using wordTrace_append hprefix tailTrace_2965167
  have hstable : (prefixWord ++ tailWord_2965167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965167).length < 2 ^ (prefixWord ++ tailWord_2965167).sum := by decide
  have hdescent : baseEnd_2965167 < baseStart_2965167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965204 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_2965204 : Nat := 118140960795 + 2965204 * 2 ^ 59
def prefixEnd_2965204 : Nat := 4983230072969 + 3 ^ 40 * 2965204 * 2
def baseEnd_2965204 : Nat := 507524963544840619804427

theorem tailTrace_2965204 : CollatzResearch.WordTrace tailWord_2965204 prefixEnd_2965204 507524963544840619804427 := by
  unfold tailWord_2965204
  simp only [CollatzResearch.WordTrace]
  refine ⟨54074937374789899685215333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72099916499719866246953777 54074937374789899685215333)
  ·
    refine ⟨10139050757773106190977875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54074937374789899685215333 10139050757773106190977875)
    ·
      refine ⟨15208576136659659286466813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10139050757773106190977875 15208576136659659286466813)
      ·
        refine ⟨5703216051247372232425055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15208576136659659286466813 5703216051247372232425055)
        ·
          refine ⟨8554824076871058348637583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5703216051247372232425055 8554824076871058348637583)
          ·
            refine ⟨12832236115306587522956375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8554824076871058348637583 12832236115306587522956375)
            ·
              refine ⟨19248354172959881284434563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12832236115306587522956375 19248354172959881284434563)
              ·
                refine ⟨28872531259439821926651845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19248354172959881284434563 28872531259439821926651845)
                ·
                  refine ⟨5413599611144966611247221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28872531259439821926651845 5413599611144966611247221)
                  ·
                    refine ⟨507524963544840619804427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5413599611144966611247221 507524963544840619804427)
                    ·
                      rfl

theorem cell23_2965204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_2965204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965204 prefixEnd_2965204 := by exact prefixLift 2965204
  have htrace : WordTrace (prefixWord ++ tailWord_2965204) baseStart_2965204 baseEnd_2965204 := by
    simpa [prefixWord, tailWord_2965204, baseEnd_2965204] using wordTrace_append hprefix tailTrace_2965204
  have hstable : (prefixWord ++ tailWord_2965204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965204).length < 2 ^ (prefixWord ++ tailWord_2965204).sum := by decide
  have hdescent : baseEnd_2965204 < baseStart_2965204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965227 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 3]
def baseStart_2965227 : Nat := 118140960795 + 2965227 * 2 ^ 59
def prefixEnd_2965227 : Nat := 4983230072969 + 3 ^ 40 * 2965227 * 2
def baseEnd_2965227 : Nat := 1522586700689575269425675

theorem tailTrace_2965227 : CollatzResearch.WordTrace tailWord_2965227 prefixEnd_2965227 1522586700689575269425675 := by
  unfold tailWord_2965227
  simp only [CollatzResearch.WordTrace]
  refine ⟨108150713628496474298517935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72100475752330982865678623 108150713628496474298517935)
  ·
    refine ⟨162226070442744711447776903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108150713628496474298517935 162226070442744711447776903)
    ·
      refine ⟨243339105664117067171665355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162226070442744711447776903 243339105664117067171665355)
      ·
        refine ⟨365008658496175600757498033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243339105664117067171665355 365008658496175600757498033)
        ·
          refine ⟨273756493872131700568123525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365008658496175600757498033 273756493872131700568123525)
          ·
            refine ⟨51329342601024693856523161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273756493872131700568123525 51329342601024693856523161)
            ·
              refine ⟨38497006950768520392392371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51329342601024693856523161 38497006950768520392392371)
              ·
                refine ⟨57745510426152780588588557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38497006950768520392392371 57745510426152780588588557)
                ·
                  refine ⟨21654566409807292720720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57745510426152780588588557 21654566409807292720720709)
                  ·
                    refine ⟨4060231201838867385135133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21654566409807292720720709 4060231201838867385135133)
                    ·
                      refine ⟨1522586700689575269425675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060231201838867385135133 1522586700689575269425675)
                      ·
                        rfl

theorem cell23_2965227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 3].length) (baseStart_2965227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965227 prefixEnd_2965227 := by exact prefixLift 2965227
  have htrace : WordTrace (prefixWord ++ tailWord_2965227) baseStart_2965227 baseEnd_2965227 := by
    simpa [prefixWord, tailWord_2965227, baseEnd_2965227] using wordTrace_append hprefix tailTrace_2965227
  have hstable : (prefixWord ++ tailWord_2965227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965227).length < 2 ^ (prefixWord ++ tailWord_2965227).sum := by decide
  have hdescent : baseEnd_2965227 < baseStart_2965227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965234 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_2965234 : Nat := 118140960795 + 2965234 * 2 ^ 59
def prefixEnd_2965234 : Nat := 4983230072969 + 3 ^ 40 * 2965234 * 2
def baseEnd_2965234 : Nat := 507530098351385580679381

theorem tailTrace_2965234 : CollatzResearch.WordTrace tailWord_2965234 prefixEnd_2965234 507530098351385580679381 := by
  unfold tailWord_2965234
  simp only [CollatzResearch.WordTrace]
  refine ⟨27037742234867778623505689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72100645959647409662681837 27037742234867778623505689)
  ·
    refine ⟨20278306676150833967629267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27037742234867778623505689 20278306676150833967629267)
    ·
      refine ⟨30417460014226250951443901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20278306676150833967629267 30417460014226250951443901)
      ·
        refine ⟨11406547505334844106791463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30417460014226250951443901 11406547505334844106791463)
        ·
          refine ⟨17109821258002266160187195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11406547505334844106791463 17109821258002266160187195)
          ·
            refine ⟨25664731887003399240280793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17109821258002266160187195 25664731887003399240280793)
            ·
              refine ⟨19248548915252549430210595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25664731887003399240280793 19248548915252549430210595)
              ·
                refine ⟨28872823372878824145315893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19248548915252549430210595 28872823372878824145315893)
                ·
                  refine ⟨2706827191207389763623365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28872823372878824145315893 2706827191207389763623365)
                  ·
                    refine ⟨507530098351385580679381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706827191207389763623365 507530098351385580679381)
                    ·
                      rfl

theorem cell23_2965234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_2965234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965234 prefixEnd_2965234 := by exact prefixLift 2965234
  have htrace : WordTrace (prefixWord ++ tailWord_2965234) baseStart_2965234 baseEnd_2965234 := by
    simpa [prefixWord, tailWord_2965234, baseEnd_2965234] using wordTrace_append hprefix tailTrace_2965234
  have hstable : (prefixWord ++ tailWord_2965234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965234).length < 2 ^ (prefixWord ++ tailWord_2965234).sum := by decide
  have hdescent : baseEnd_2965234 < baseStart_2965234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965308 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_2965308 : Nat := 118140960795 + 2965308 * 2 ^ 59
def prefixEnd_2965308 : Nat := 4983230072969 + 3 ^ 40 * 2965308 * 2
def baseEnd_2965308 : Nat := 1522628292622589452512803

theorem tailTrace_2965308 : CollatzResearch.WordTrace tailWord_2965308 prefixEnd_2965308 1522628292622589452512803 := by
  unfold tailWord_2965308
  simp only [CollatzResearch.WordTrace]
  refine ⟨54076833970601512566108289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72102445294135350088144385 54076833970601512566108289)
  ·
    refine ⟨40557625477951134424581217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54076833970601512566108289 40557625477951134424581217)
    ·
      refine ⟨30418219108463350818435913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40557625477951134424581217 30418219108463350818435913)
      ·
        refine ⟨22813664331347513113826935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30418219108463350818435913 22813664331347513113826935)
        ·
          refine ⟨34220496497021269670740403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22813664331347513113826935 34220496497021269670740403)
          ·
            refine ⟨51330744745531904506110605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34220496497021269670740403 51330744745531904506110605)
            ·
              refine ⟨19249029279574464189791477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51330744745531904506110605 19249029279574464189791477)
              ·
                refine ⟨1804596494960106017792951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19249029279574464189791477 1804596494960106017792951)
                ·
                  refine ⟨2706894742440159026689427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804596494960106017792951 2706894742440159026689427)
                  ·
                    refine ⟨4060342113660238540034141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706894742440159026689427 4060342113660238540034141)
                    ·
                      refine ⟨1522628292622589452512803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060342113660238540034141 1522628292622589452512803)
                      ·
                        rfl

theorem cell23_2965308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_2965308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965308 prefixEnd_2965308 := by exact prefixLift 2965308
  have htrace : WordTrace (prefixWord ++ tailWord_2965308) baseStart_2965308 baseEnd_2965308 := by
    simpa [prefixWord, tailWord_2965308, baseEnd_2965308] using wordTrace_append hprefix tailTrace_2965308
  have hstable : (prefixWord ++ tailWord_2965308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965308).length < 2 ^ (prefixWord ++ tailWord_2965308).sum := by decide
  have hdescent : baseEnd_2965308 < baseStart_2965308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965311 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 1, 5]
def baseStart_2965311 : Nat := 118140960795 + 2965311 * 2 ^ 59
def prefixEnd_2965311 : Nat := 4983230072969 + 3 ^ 40 * 2965311 * 2
def baseEnd_2965311 : Nat := 507543277688184313591763

theorem tailTrace_2965311 : CollatzResearch.WordTrace tailWord_2965311 prefixEnd_2965311 507543277688184313591763 := by
  unfold tailWord_2965311
  simp only [CollatzResearch.WordTrace]
  refine ⟨108153777360192156644575787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72102518240128104429717191 108153777360192156644575787)
  ·
    refine ⟨162230666040288234966863681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108153777360192156644575787 162230666040288234966863681)
    ·
      refine ⟨121672999530216176225147761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162230666040288234966863681 121672999530216176225147761)
      ·
        refine ⟨91254749647662132168860821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121672999530216176225147761 91254749647662132168860821)
        ·
          refine ⟨4277566389734162445415351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91254749647662132168860821 4277566389734162445415351)
          ·
            refine ⟨6416349584601243668123027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277566389734162445415351 6416349584601243668123027)
            ·
              refine ⟨9624524376901865502184541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416349584601243668123027 9624524376901865502184541)
              ·
                refine ⟨3609196641338199563319203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9624524376901865502184541 3609196641338199563319203)
                ·
                  refine ⟨5413794962007299344978805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609196641338199563319203 5413794962007299344978805)
                  ·
                    refine ⟨507543277688184313591763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5413794962007299344978805 507543277688184313591763)
                    ·
                      rfl

theorem cell23_2965311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_2965311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965311 prefixEnd_2965311 := by exact prefixLift 2965311
  have htrace : WordTrace (prefixWord ++ tailWord_2965311) baseStart_2965311 baseEnd_2965311 := by
    simpa [prefixWord, tailWord_2965311, baseEnd_2965311] using wordTrace_append hprefix tailTrace_2965311
  have hstable : (prefixWord ++ tailWord_2965311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965311).length < 2 ^ (prefixWord ++ tailWord_2965311).sum := by decide
  have hdescent : baseEnd_2965311 < baseStart_2965311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965325 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2965325 : Nat := 118140960795 + 2965325 * 2 ^ 59
def prefixEnd_2965325 : Nat := 4983230072969 + 3 ^ 40 * 2965325 * 2
def baseEnd_2965325 : Nat := 1522637021793715886000225

theorem tailTrace_2965325 : CollatzResearch.WordTrace tailWord_2965325 prefixEnd_2965325 1522637021793715886000225 := by
  unfold tailWord_2965325
  simp only [CollatzResearch.WordTrace]
  refine ⟨108154287982141437035585429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72102858654760958023723619 108154287982141437035585429)
  ·
    refine ⟨5069732249162879861043067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108154287982141437035585429 5069732249162879861043067)
    ·
      refine ⟨7604598373744319791564601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5069732249162879861043067 7604598373744319791564601)
      ·
        refine ⟨5703448780308239843673451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7604598373744319791564601 5703448780308239843673451)
        ·
          refine ⟨8555173170462359765510177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5703448780308239843673451 8555173170462359765510177)
          ·
            refine ⟨6416379877846769824132633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8555173170462359765510177 6416379877846769824132633)
            ·
              refine ⟨4812284908385077368099475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6416379877846769824132633 4812284908385077368099475)
              ·
                refine ⟨7218427362577616052149213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4812284908385077368099475 7218427362577616052149213)
                ·
                  refine ⟨2706910260966606019555955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7218427362577616052149213 2706910260966606019555955)
                  ·
                    refine ⟨4060365391449909029333933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706910260966606019555955 4060365391449909029333933)
                    ·
                      refine ⟨1522637021793715886000225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060365391449909029333933 1522637021793715886000225)
                      ·
                        rfl

theorem cell23_2965325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2965325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965325 prefixEnd_2965325 := by exact prefixLift 2965325
  have htrace : WordTrace (prefixWord ++ tailWord_2965325) baseStart_2965325 baseEnd_2965325 := by
    simpa [prefixWord, tailWord_2965325, baseEnd_2965325] using wordTrace_append hprefix tailTrace_2965325
  have hstable : (prefixWord ++ tailWord_2965325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965325).length < 2 ^ (prefixWord ++ tailWord_2965325).sum := by decide
  have hdescent : baseEnd_2965325 < baseStart_2965325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965327 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_2965327 : Nat := 118140960795 + 2965327 * 2 ^ 59
def prefixEnd_2965327 : Nat := 4983230072969 + 3 ^ 40 * 2965327 * 2
def baseEnd_2965327 : Nat := 1522638048755024878175215

theorem tailTrace_2965327 : CollatzResearch.WordTrace tailWord_2965327 prefixEnd_2965327 1522638048755024878175215 := by
  unfold tailWord_2965327
  simp only [CollatzResearch.WordTrace]
  refine ⟨108154360928134191377158235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72102907285422794251438823 108154360928134191377158235)
  ·
    refine ⟨162231541392201287065737353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108154360928134191377158235 162231541392201287065737353)
    ·
      refine ⟨121673656044150965299303015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162231541392201287065737353 121673656044150965299303015)
      ·
        refine ⟨182510484066226447948954523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121673656044150965299303015 182510484066226447948954523)
        ·
          refine ⟨273765726099339671923431785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182510484066226447948954523 273765726099339671923431785)
          ·
            refine ⟨205324294574504753942573839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273765726099339671923431785 205324294574504753942573839)
            ·
              refine ⟨307986441861757130913860759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205324294574504753942573839 307986441861757130913860759)
              ·
                refine ⟨461979662792635696370791139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307986441861757130913860759 461979662792635696370791139)
                ·
                  refine ⟨692969494188953544556186709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461979662792635696370791139 692969494188953544556186709)
                  ·
                    refine ⟨8120736260026799350267813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 692969494188953544556186709 8120736260026799350267813)
                    ·
                      refine ⟨1522638048755024878175215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8120736260026799350267813 1522638048755024878175215)
                      ·
                        rfl

theorem cell23_2965327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_2965327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965327 prefixEnd_2965327 := by exact prefixLift 2965327
  have htrace : WordTrace (prefixWord ++ tailWord_2965327) baseStart_2965327 baseEnd_2965327 := by
    simpa [prefixWord, tailWord_2965327, baseEnd_2965327] using wordTrace_append hprefix tailTrace_2965327
  have hstable : (prefixWord ++ tailWord_2965327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965327).length < 2 ^ (prefixWord ++ tailWord_2965327).sum := by decide
  have hdescent : baseEnd_2965327 < baseStart_2965327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965337 : List Nat := [1, 2, 1, 2, 2, 3, 2, 10]
def baseStart_2965337 : Nat := 118140960795 + 2965337 * 2 ^ 59
def prefixEnd_2965337 : Nat := 4983230072969 + 3 ^ 40 * 2965337 * 2
def baseEnd_2965337 : Nat := 56394191983761845890747

theorem tailTrace_2965337 : CollatzResearch.WordTrace tailWord_2965337 prefixEnd_2965337 56394191983761845890747 := by
  unfold tailWord_2965337
  simp only [CollatzResearch.WordTrace]
  refine ⟨108154725658097963085022265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72103150438731975390014843 108154725658097963085022265)
  ·
    refine ⟨81116044243573472313766699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108154725658097963085022265 81116044243573472313766699)
    ·
      refine ⟨121674066365360208470650049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81116044243573472313766699 121674066365360208470650049)
      ·
        refine ⟨91255549774020156352987537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121674066365360208470650049 91255549774020156352987537)
        ·
          refine ⟨68441662330515117264740653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91255549774020156352987537 68441662330515117264740653)
          ·
            refine ⟨25665623373943168974277745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68441662330515117264740653 25665623373943168974277745)
            ·
              refine ⟨19249217530457376730708309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25665623373943168974277745 19249217530457376730708309)
              ·
                refine ⟨56394191983761845890747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19249217530457376730708309 56394191983761845890747)
                ·
                  rfl

theorem cell23_2965337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 10].length) (baseStart_2965337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965337 prefixEnd_2965337 := by exact prefixLift 2965337
  have htrace : WordTrace (prefixWord ++ tailWord_2965337) baseStart_2965337 baseEnd_2965337 := by
    simpa [prefixWord, tailWord_2965337, baseEnd_2965337] using wordTrace_append hprefix tailTrace_2965337
  have hstable : (prefixWord ++ tailWord_2965337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965337).length < 2 ^ (prefixWord ++ tailWord_2965337).sum := by decide
  have hdescent : baseEnd_2965337 < baseStart_2965337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965344 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_2965344 : Nat := 118140960795 + 2965344 * 2 ^ 59
def prefixEnd_2965344 : Nat := 4983230072969 + 3 ^ 40 * 2965344 * 2
def baseEnd_2965344 : Nat := 1522646777926151311662637

theorem tailTrace_2965344 : CollatzResearch.WordTrace tailWord_2965344 prefixEnd_2965344 1522646777926151311662637 := by
  unfold tailWord_2965344
  simp only [CollatzResearch.WordTrace]
  refine ⟨54077490484536301640263543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72103320646048402187018057 54077490484536301640263543)
  ·
    refine ⟨81116235726804452460395315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54077490484536301640263543 81116235726804452460395315)
    ·
      refine ⟨121674353590206678690592973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81116235726804452460395315 121674353590206678690592973)
      ·
        refine ⟨45627882596327504508972365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121674353590206678690592973 45627882596327504508972365)
        ·
          refine ⟨17110455973622814190864637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45627882596327504508972365 17110455973622814190864637)
          ·
            refine ⟨6416420990108555321574239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17110455973622814190864637 6416420990108555321574239)
            ·
              refine ⟨9624631485162832982361359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416420990108555321574239 9624631485162832982361359)
              ·
                refine ⟨14436947227744249473542039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9624631485162832982361359 14436947227744249473542039)
                ·
                  refine ⟨21655420841616374210313059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14436947227744249473542039 21655420841616374210313059)
                  ·
                    refine ⟨32483131262424561315469589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21655420841616374210313059 32483131262424561315469589)
                    ·
                      refine ⟨1522646777926151311662637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32483131262424561315469589 1522646777926151311662637)
                      ·
                        rfl

theorem cell23_2965344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_2965344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965344 prefixEnd_2965344 := by exact prefixLift 2965344
  have htrace : WordTrace (prefixWord ++ tailWord_2965344) baseStart_2965344 baseEnd_2965344 := by
    simpa [prefixWord, tailWord_2965344, baseEnd_2965344] using wordTrace_append hprefix tailTrace_2965344
  have hstable : (prefixWord ++ tailWord_2965344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965344).length < 2 ^ (prefixWord ++ tailWord_2965344).sum := by decide
  have hdescent : baseEnd_2965344 < baseStart_2965344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965348 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_2965348 : Nat := 118140960795 + 2965348 * 2 ^ 59
def prefixEnd_2965348 : Nat := 4983230072969 + 3 ^ 40 * 2965348 * 2
def baseEnd_2965348 : Nat := 1522648831848769296012619

theorem tailTrace_2965348 : CollatzResearch.WordTrace tailWord_2965348 prefixEnd_2965348 1522648831848769296012619 := by
  unfold tailWord_2965348
  simp only [CollatzResearch.WordTrace]
  refine ⟨54077563430529055981836349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72103417907372074642448465 54077563430529055981836349)
  ·
    refine ⟨20279086286448395993188631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54077563430529055981836349 20279086286448395993188631)
    ·
      refine ⟨30418629429672593989782947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20279086286448395993188631 30418629429672593989782947)
      ·
        refine ⟨45627944144508890984674421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30418629429672593989782947 45627944144508890984674421)
        ·
          refine ⟨4277619763547708529813227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45627944144508890984674421 4277619763547708529813227)
          ·
            refine ⟨6416429645321562794719841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277619763547708529813227 6416429645321562794719841)
            ·
              refine ⟨4812322233991172096039881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6416429645321562794719841 4812322233991172096039881)
              ·
                refine ⟨3609241675493379072029911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812322233991172096039881 3609241675493379072029911)
                ·
                  refine ⟨5413862513240068608044867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609241675493379072029911 5413862513240068608044867)
                  ·
                    refine ⟨8120793769860102912067301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413862513240068608044867 8120793769860102912067301)
                    ·
                      refine ⟨1522648831848769296012619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8120793769860102912067301 1522648831848769296012619)
                      ·
                        rfl

theorem cell23_2965348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_2965348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965348 prefixEnd_2965348 := by exact prefixLift 2965348
  have htrace : WordTrace (prefixWord ++ tailWord_2965348) baseStart_2965348 baseEnd_2965348 := by
    simpa [prefixWord, tailWord_2965348, baseEnd_2965348] using wordTrace_append hprefix tailTrace_2965348
  have hstable : (prefixWord ++ tailWord_2965348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965348).length < 2 ^ (prefixWord ++ tailWord_2965348).sum := by decide
  have hdescent : baseEnd_2965348 < baseStart_2965348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965367 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 9]
def baseStart_2965367 : Nat := 118140960795 + 2965367 * 2 ^ 59
def prefixEnd_2965367 : Nat := 4983230072969 + 3 ^ 40 * 2965367 * 2
def baseEnd_2965367 : Nat := 507552862660401573891677

theorem tailTrace_2965367 : CollatzResearch.WordTrace tailWord_2965367 prefixEnd_2965367 507552862660401573891677 := by
  unfold tailWord_2965367
  simp only [CollatzResearch.WordTrace]
  refine ⟨108155819847989278208614355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72103879898659518805742903 108155819847989278208614355)
  ·
    refine ⟨162233729771983917312921533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108155819847989278208614355 162233729771983917312921533)
    ·
      refine ⟨60837648664493968992345575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162233729771983917312921533 60837648664493968992345575)
      ·
        refine ⟨91256472996740953488518363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60837648664493968992345575 91256472996740953488518363)
        ·
          refine ⟨136884709495111430232777545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91256472996740953488518363 136884709495111430232777545)
          ·
            refine ⟨102663532121333572674583159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136884709495111430232777545 102663532121333572674583159)
            ·
              refine ⟨153995298182000359011874739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102663532121333572674583159 153995298182000359011874739)
              ·
                refine ⟨230992947273000538517812109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153995298182000359011874739 230992947273000538517812109)
                ·
                  refine ⟨86622355227375201944179541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230992947273000538517812109 86622355227375201944179541)
                  ·
                    refine ⟨507552862660401573891677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86622355227375201944179541 507552862660401573891677)
                    ·
                      rfl

theorem cell23_2965367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_2965367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965367 prefixEnd_2965367 := by exact prefixLift 2965367
  have htrace : WordTrace (prefixWord ++ tailWord_2965367) baseStart_2965367 baseEnd_2965367 := by
    simpa [prefixWord, tailWord_2965367, baseEnd_2965367] using wordTrace_append hprefix tailTrace_2965367
  have hstable : (prefixWord ++ tailWord_2965367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965367).length < 2 ^ (prefixWord ++ tailWord_2965367).sum := by decide
  have hdescent : baseEnd_2965367 < baseStart_2965367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965381 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_2965381 : Nat := 118140960795 + 2965381 * 2 ^ 59
def prefixEnd_2965381 : Nat := 4983230072969 + 3 ^ 40 * 2965381 * 2
def baseEnd_2965381 : Nat := 1522665776710367666899967

theorem tailTrace_2965381 : CollatzResearch.WordTrace tailWord_2965381 prefixEnd_2965381 1522665776710367666899967 := by
  unfold tailWord_2965381
  simp only [CollatzResearch.WordTrace]
  refine ⟨108156330469938558599623997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72104220313292372399749331 108156330469938558599623997)
  ·
    refine ⟨40558623926226959474858999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108156330469938558599623997 40558623926226959474858999)
    ·
      refine ⟨60837935889340439212288499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40558623926226959474858999 60837935889340439212288499)
      ·
        refine ⟨91256903834010658818432749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60837935889340439212288499 91256903834010658818432749)
        ·
          refine ⟨34221338937753997056912281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91256903834010658818432749 34221338937753997056912281)
          ·
            refine ⟨25666004203315497792684211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34221338937753997056912281 25666004203315497792684211)
            ·
              refine ⟨38499006304973246689026317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25666004203315497792684211 38499006304973246689026317)
              ·
                refine ⟨14437127364364967508384869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38499006304973246689026317 14437127364364967508384869)
                ·
                  refine ⟨2706961380818431407822163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14437127364364967508384869 2706961380818431407822163)
                  ·
                    refine ⟨4060442071227647111733245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706961380818431407822163 4060442071227647111733245)
                    ·
                      refine ⟨1522665776710367666899967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060442071227647111733245 1522665776710367666899967)
                      ·
                        rfl

theorem cell23_2965381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_2965381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965381 prefixEnd_2965381 := by exact prefixLift 2965381
  have htrace : WordTrace (prefixWord ++ tailWord_2965381) baseStart_2965381 baseEnd_2965381 := by
    simpa [prefixWord, tailWord_2965381, baseEnd_2965381] using wordTrace_append hprefix tailTrace_2965381
  have hstable : (prefixWord ++ tailWord_2965381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965381).length < 2 ^ (prefixWord ++ tailWord_2965381).sum := by decide
  have hdescent : baseEnd_2965381 < baseStart_2965381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965424 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_2965424 : Nat := 118140960795 + 2965424 * 2 ^ 59
def prefixEnd_2965424 : Nat := 4983230072969 + 3 ^ 40 * 2965424 * 2
def baseEnd_2965424 : Nat := 1522687856378510998662269

theorem tailTrace_2965424 : CollatzResearch.WordTrace tailWord_2965424 prefixEnd_2965424 1522687856378510998662269 := by
  unfold tailWord_2965424
  simp only [CollatzResearch.WordTrace]
  refine ⟨54078949404391388471719663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72105265872521851295626217 54078949404391388471719663)
  ·
    refine ⟨81118424106587082707579495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54078949404391388471719663 81118424106587082707579495)
    ·
      refine ⟨121677636159880624061369243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81118424106587082707579495 121677636159880624061369243)
      ·
        refine ⟨182516454239820936092053865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121677636159880624061369243 182516454239820936092053865)
        ·
          refine ⟨136887340679865702069040399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182516454239820936092053865 136887340679865702069040399)
          ·
            refine ⟨205331011019798553103560599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136887340679865702069040399 205331011019798553103560599)
            ·
              refine ⟨307996516529697829655340899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205331011019798553103560599 307996516529697829655340899)
              ·
                refine ⟨461994774794546744483011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307996516529697829655340899 461994774794546744483011349)
                ·
                  refine ⟨21656005068494378647641157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 461994774794546744483011349 21656005068494378647641157)
                  ·
                    refine ⟨4060500950342695996432717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21656005068494378647641157 4060500950342695996432717)
                    ·
                      refine ⟨1522687856378510998662269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060500950342695996432717 1522687856378510998662269)
                      ·
                        rfl

theorem cell23_2965424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_2965424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965424 prefixEnd_2965424 := by exact prefixLift 2965424
  have htrace : WordTrace (prefixWord ++ tailWord_2965424) baseStart_2965424 baseEnd_2965424 := by
    simpa [prefixWord, tailWord_2965424, baseEnd_2965424] using wordTrace_append hprefix tailTrace_2965424
  have hstable : (prefixWord ++ tailWord_2965424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965424).length < 2 ^ (prefixWord ++ tailWord_2965424).sum := by decide
  have hdescent : baseEnd_2965424 < baseStart_2965424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965461 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 7]
def baseStart_2965461 : Nat := 118140960795 + 2965461 * 2 ^ 59
def prefixEnd_2965461 : Nat := 4983230072969 + 3 ^ 40 * 2965461 * 2
def baseEnd_2965461 : Nat := 169189650573636372655511

theorem tailTrace_2965461 : CollatzResearch.WordTrace tailWord_2965461 prefixEnd_2965461 169189650573636372655511 := by
  unfold tailWord_2965461
  simp only [CollatzResearch.WordTrace]
  refine ⟨108159248309648732262536237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72106165539765821508357491 108159248309648732262536237)
  ·
    refine ⟨40559718116118274598451089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108159248309648732262536237 40559718116118274598451089)
    ·
      refine ⟨30419788587088705948838317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40559718116118274598451089 30419788587088705948838317)
      ·
        refine ⟨11407420720158264730814369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30419788587088705948838317 11407420720158264730814369)
        ·
          refine ⟨8555565540118698548110777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11407420720158264730814369 8555565540118698548110777)
          ·
            refine ⟨6416674155089023911083083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8555565540118698548110777 6416674155089023911083083)
            ·
              refine ⟨9625011232633535866624625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416674155089023911083083 9625011232633535866624625)
              ·
                refine ⟨7218758424475151899968469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9625011232633535866624625 7218758424475151899968469)
                ·
                  refine ⟨169189650573636372655511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7218758424475151899968469 169189650573636372655511)
                  ·
                    rfl

theorem cell23_2965461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_2965461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965461 prefixEnd_2965461 := by exact prefixLift 2965461
  have htrace : WordTrace (prefixWord ++ tailWord_2965461) baseStart_2965461 baseEnd_2965461 := by
    simpa [prefixWord, tailWord_2965461, baseEnd_2965461] using wordTrace_append hprefix tailTrace_2965461
  have hstable : (prefixWord ++ tailWord_2965461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965461).length < 2 ^ (prefixWord ++ tailWord_2965461).sum := by decide
  have hdescent : baseEnd_2965461 < baseStart_2965461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965484 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2965484 : Nat := 118140960795 + 2965484 * 2 ^ 59
def prefixEnd_2965484 : Nat := 4983230072969 + 3 ^ 40 * 2965484 * 2
def baseEnd_2965484 : Nat := 1522718665217780763911993

theorem tailTrace_2965484 : CollatzResearch.WordTrace tailWord_2965484 prefixEnd_2965484 1522718665217780763911993 := by
  unfold tailWord_2965484
  simp only [CollatzResearch.WordTrace]
  refine ⟨54080043594282703595311753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72106724792376938127082337 54080043594282703595311753)
  ·
    refine ⟨40560032695712027696483815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54080043594282703595311753 40560032695712027696483815)
    ·
      refine ⟨60840049043568041544725723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40560032695712027696483815 60840049043568041544725723)
      ·
        refine ⟨91260073565352062317088585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60840049043568041544725723 91260073565352062317088585)
        ·
          refine ⟨68445055174014046737816439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91260073565352062317088585 68445055174014046737816439)
          ·
            refine ⟨102667582761021070106724659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68445055174014046737816439 102667582761021070106724659)
            ·
              refine ⟨154001374141531605160086989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102667582761021070106724659 154001374141531605160086989)
              ·
                refine ⟨57750515303074351935032621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154001374141531605160086989 57750515303074351935032621)
                ·
                  refine ⟨21656443238652881975637233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57750515303074351935032621 21656443238652881975637233)
                  ·
                    refine ⟨16242332428989661481727925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21656443238652881975637233 16242332428989661481727925)
                    ·
                      refine ⟨1522718665217780763911993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16242332428989661481727925 1522718665217780763911993)
                      ·
                        rfl

theorem cell23_2965484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2965484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965484 prefixEnd_2965484 := by exact prefixLift 2965484
  have htrace : WordTrace (prefixWord ++ tailWord_2965484) baseStart_2965484 baseEnd_2965484 := by
    simpa [prefixWord, tailWord_2965484, baseEnd_2965484] using wordTrace_append hprefix tailTrace_2965484
  have hstable : (prefixWord ++ tailWord_2965484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965484).length < 2 ^ (prefixWord ++ tailWord_2965484).sum := by decide
  have hdescent : baseEnd_2965484 < baseStart_2965484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965489 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 2, 2, 2]
def baseStart_2965489 : Nat := 118140960795 + 2965489 * 2 ^ 59
def prefixEnd_2965489 : Nat := 4983230072969 + 3 ^ 40 * 2965489 * 2
def baseEnd_2965489 : Nat := 1522721232621053244349471

theorem tailTrace_2965489 : CollatzResearch.WordTrace tailWord_2965489 prefixEnd_2965489 1522721232621053244349471 := by
  unfold tailWord_2965489
  simp only [CollatzResearch.WordTrace]
  refine ⟨108160269553547293044555521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72106846369031528696370347 108160269553547293044555521)
  ·
    refine ⟨81120202165160469783416641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108160269553547293044555521 81120202165160469783416641)
    ·
      refine ⟨60840151623870352337562481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81120202165160469783416641 60840151623870352337562481)
      ·
        refine ⟨45630113717902764253171861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60840151623870352337562481 45630113717902764253171861)
        ·
          refine ⟨2138911580526692074367431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45630113717902764253171861 2138911580526692074367431)
          ·
            refine ⟨3208367370790038111551147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138911580526692074367431 3208367370790038111551147)
            ·
              refine ⟨4812551056185057167326721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208367370790038111551147 4812551056185057167326721)
              ·
                refine ⟨3609413292138792875495041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812551056185057167326721 3609413292138792875495041)
                ·
                  refine ⟨2707059969104094656621281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3609413292138792875495041 2707059969104094656621281)
                  ·
                    refine ⟨2030294976828070992465961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2707059969104094656621281 2030294976828070992465961)
                    ·
                      refine ⟨1522721232621053244349471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030294976828070992465961 1522721232621053244349471)
                      ·
                        rfl

theorem cell23_2965489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_2965489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965489 prefixEnd_2965489 := by exact prefixLift 2965489
  have htrace : WordTrace (prefixWord ++ tailWord_2965489) baseStart_2965489 baseEnd_2965489 := by
    simpa [prefixWord, tailWord_2965489, baseEnd_2965489] using wordTrace_append hprefix tailTrace_2965489
  have hstable : (prefixWord ++ tailWord_2965489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965489).length < 2 ^ (prefixWord ++ tailWord_2965489).sum := by decide
  have hdescent : baseEnd_2965489 < baseStart_2965489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965511 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2965511 : Nat := 118140960795 + 2965511 * 2 ^ 59
def prefixEnd_2965511 : Nat := 4983230072969 + 3 ^ 40 * 2965511 * 2
def baseEnd_2965511 : Nat := 1522732529195452158274369

theorem tailTrace_2965511 : CollatzResearch.WordTrace tailWord_2965511 prefixEnd_2965511 1522732529195452158274369 := by
  unfold tailWord_2965511
  simp only [CollatzResearch.WordTrace]
  refine ⟨108161071959467590801856387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72107381306311727201237591 108161071959467590801856387)
  ·
    refine ⟨162241607939201386202784581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108161071959467590801856387 162241607939201386202784581)
    ·
      refine ⟨30420301488600259913022109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162241607939201386202784581 30420301488600259913022109)
      ·
        refine ⟨11407613058225097467383291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30420301488600259913022109 11407613058225097467383291)
        ·
          refine ⟨17111419587337646201074937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11407613058225097467383291 17111419587337646201074937)
          ·
            refine ⟨12833564690503234650806203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17111419587337646201074937 12833564690503234650806203)
            ·
              refine ⟨19250347035754851976209305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12833564690503234650806203 19250347035754851976209305)
              ·
                refine ⟨14437760276816138982156979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19250347035754851976209305 14437760276816138982156979)
                ·
                  refine ⟨21656640415224208473235469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14437760276816138982156979 21656640415224208473235469)
                  ·
                    refine ⟨8121240155709078177463301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21656640415224208473235469 8121240155709078177463301)
                    ·
                      refine ⟨1522732529195452158274369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8121240155709078177463301 1522732529195452158274369)
                      ·
                        rfl

theorem cell23_2965511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2965511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965511 prefixEnd_2965511 := by exact prefixLift 2965511
  have htrace : WordTrace (prefixWord ++ tailWord_2965511) baseStart_2965511 baseEnd_2965511 := by
    simpa [prefixWord, tailWord_2965511, baseEnd_2965511] using wordTrace_append hprefix tailTrace_2965511
  have hstable : (prefixWord ++ tailWord_2965511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965511).length < 2 ^ (prefixWord ++ tailWord_2965511).sum := by decide
  have hdescent : baseEnd_2965511 < baseStart_2965511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965568 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 6]
def baseStart_2965568 : Nat := 118140960795 + 2965568 * 2 ^ 59
def prefixEnd_2965568 : Nat := 4983230072969 + 3 ^ 40 * 2965568 * 2
def baseEnd_2965568 : Nat := 169195755288084270584623

theorem tailTrace_2965568 : CollatzResearch.WordTrace tailWord_2965568 prefixEnd_2965568 169195755288084270584623 := by
  unfold tailWord_2965568
  simp only [CollatzResearch.WordTrace]
  refine ⟨54081575460130544768340679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72108767280174059691120905 54081575460130544768340679)
  ·
    refine ⟨81122363190195817152511019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54081575460130544768340679 81122363190195817152511019)
    ·
      refine ⟨121683544785293725728766529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81122363190195817152511019 121683544785293725728766529)
      ·
        refine ⟨91262658588970294296574897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121683544785293725728766529 91262658588970294296574897)
        ·
          refine ⟨68446993941727720722431173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91262658588970294296574897 68446993941727720722431173)
          ·
            refine ⟨12833811364073947635455845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68446993941727720722431173 12833811364073947635455845)
            ·
              refine ⟨2406339630763865181647971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12833811364073947635455845 2406339630763865181647971)
              ·
                refine ⟨3609509446145797772471957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406339630763865181647971 3609509446145797772471957)
                ·
                  refine ⟨169195755288084270584623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3609509446145797772471957 169195755288084270584623)
                  ·
                    rfl

theorem cell23_2965568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 6].length) (baseStart_2965568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965568 prefixEnd_2965568 := by exact prefixLift 2965568
  have htrace : WordTrace (prefixWord ++ tailWord_2965568) baseStart_2965568 baseEnd_2965568 := by
    simpa [prefixWord, tailWord_2965568, baseEnd_2965568] using wordTrace_append hprefix tailTrace_2965568
  have hstable : (prefixWord ++ tailWord_2965568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965568).length < 2 ^ (prefixWord ++ tailWord_2965568).sum := by decide
  have hdescent : baseEnd_2965568 < baseStart_2965568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965578 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_2965578 : Nat := 118140960795 + 2965578 * 2 ^ 59
def prefixEnd_2965578 : Nat := 4983230072969 + 3 ^ 40 * 2965578 * 2
def baseEnd_2965578 : Nat := 1522766932399303396136561

theorem tailTrace_2965578 : CollatzResearch.WordTrace tailWord_2965578 prefixEnd_2965578 1522766932399303396136561 := by
  unfold tailWord_2965578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27040878912556215311136347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72109010433483240829696925 27040878912556215311136347)
  ·
    refine ⟨40561318368834322966704521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27040878912556215311136347 40561318368834322966704521)
    ·
      refine ⟨30420988776625742225028391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40561318368834322966704521 30420988776625742225028391)
      ·
        refine ⟨45631483164938613337542587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30420988776625742225028391 45631483164938613337542587)
        ·
          refine ⟨68447224747407920006313881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45631483164938613337542587 68447224747407920006313881)
          ·
            refine ⟨51335418560555940004735411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68447224747407920006313881 51335418560555940004735411)
            ·
              refine ⟨77003127840833910007103117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51335418560555940004735411 77003127840833910007103117)
              ·
                refine ⟨28876172940312716252663669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77003127840833910007103117 28876172940312716252663669)
                ·
                  refine ⟨2707141213154317148687219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28876172940312716252663669 2707141213154317148687219)
                  ·
                    refine ⟨4060711819731475723030829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707141213154317148687219 4060711819731475723030829)
                    ·
                      refine ⟨1522766932399303396136561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060711819731475723030829 1522766932399303396136561)
                      ·
                        rfl

theorem cell23_2965578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_2965578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965578 prefixEnd_2965578 := by exact prefixLift 2965578
  have htrace : WordTrace (prefixWord ++ tailWord_2965578) baseStart_2965578 baseEnd_2965578 := by
    simpa [prefixWord, tailWord_2965578, baseEnd_2965578] using wordTrace_append hprefix tailTrace_2965578
  have hstable : (prefixWord ++ tailWord_2965578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965578).length < 2 ^ (prefixWord ++ tailWord_2965578).sum := by decide
  have hdescent : baseEnd_2965578 < baseStart_2965578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965605 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 2, 3, 2]
def baseStart_2965605 : Nat := 118140960795 + 2965605 * 2 ^ 59
def prefixEnd_2965605 : Nat := 4983230072969 + 3 ^ 40 * 2965605 * 2
def baseEnd_2965605 : Nat := 1522780796376974790498937

theorem tailTrace_2965605 : CollatzResearch.WordTrace tailWord_2965605 prefixEnd_2965605 1522780796376974790498937 := by
  unfold tailWord_2965605
  simp only [CollatzResearch.WordTrace]
  refine ⟨108164500421127044855778269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72109666947418029903852179 108164500421127044855778269)
  ·
    refine ⟨40561687657922641820916851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108164500421127044855778269 40561687657922641820916851)
    ·
      refine ⟨60842531486883962731375277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40561687657922641820916851 60842531486883962731375277)
      ·
        refine ⟨22815949307581486024265729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60842531486883962731375277 22815949307581486024265729)
        ·
          refine ⟨17111961980686114518199297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22815949307581486024265729 17111961980686114518199297)
          ·
            refine ⟨12833971485514585888649473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17111961980686114518199297 12833971485514585888649473)
            ·
              refine ⟨9625478614135939416487105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12833971485514585888649473 9625478614135939416487105)
              ·
                refine ⟨7219108960601954562365329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9625478614135939416487105 7219108960601954562365329)
                ·
                  refine ⟨5414331720451465921773997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7219108960601954562365329 5414331720451465921773997)
                  ·
                    refine ⟨2030374395169299720665249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5414331720451465921773997 2030374395169299720665249)
                    ·
                      refine ⟨1522780796376974790498937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030374395169299720665249 1522780796376974790498937)
                      ·
                        rfl

theorem cell23_2965605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_2965605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965605 prefixEnd_2965605 := by exact prefixLift 2965605
  have htrace : WordTrace (prefixWord ++ tailWord_2965605) baseStart_2965605 baseEnd_2965605 := by
    simpa [prefixWord, tailWord_2965605, baseEnd_2965605] using wordTrace_append hprefix tailTrace_2965605
  have hstable : (prefixWord ++ tailWord_2965605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965605).length < 2 ^ (prefixWord ++ tailWord_2965605).sum := by decide
  have hdescent : baseEnd_2965605 < baseStart_2965605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965612 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 1, 1, 3]
def baseStart_2965612 : Nat := 118140960795 + 2965612 * 2 ^ 59
def prefixEnd_2965612 : Nat := 4983230072969 + 3 ^ 40 * 2965612 * 2
def baseEnd_2965612 : Nat := 1522784390741556263111405

theorem tailTrace_2965612 : CollatzResearch.WordTrace tailWord_2965612 prefixEnd_2965612 1522784390741556263111405 := by
  unfold tailWord_2965612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54082377866050842525641545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72109837154734456700855393 54082377866050842525641545)
  ·
    refine ⟨40561783399538131894231159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54082377866050842525641545 40561783399538131894231159)
    ·
      refine ⟨60842675099307197841346739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40561783399538131894231159 60842675099307197841346739)
      ·
        refine ⟨91264012648960796762020109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60842675099307197841346739 91264012648960796762020109)
        ·
          refine ⟨34224004743360298785757541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91264012648960796762020109 34224004743360298785757541)
          ·
            refine ⟨6417000889380056022329539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34224004743360298785757541 6417000889380056022329539)
            ·
              refine ⟨9625501334070084033494309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417000889380056022329539 9625501334070084033494309)
              ·
                refine ⟨1804781500138140756280183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9625501334070084033494309 1804781500138140756280183)
                ·
                  refine ⟨2707172250207211134420275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804781500138140756280183 2707172250207211134420275)
                  ·
                    refine ⟨4060758375310816701630413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707172250207211134420275 4060758375310816701630413)
                    ·
                      refine ⟨1522784390741556263111405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060758375310816701630413 1522784390741556263111405)
                      ·
                        rfl

theorem cell23_2965612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_2965612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965612 prefixEnd_2965612 := by exact prefixLift 2965612
  have htrace : WordTrace (prefixWord ++ tailWord_2965612) baseStart_2965612 baseEnd_2965612 := by
    simpa [prefixWord, tailWord_2965612, baseEnd_2965612] using wordTrace_append hprefix tailTrace_2965612
  have hstable : (prefixWord ++ tailWord_2965612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965612).length < 2 ^ (prefixWord ++ tailWord_2965612).sum := by decide
  have hdescent : baseEnd_2965612 < baseStart_2965612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965618 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2965618 : Nat := 118140960795 + 2965618 * 2 ^ 59
def prefixEnd_2965618 : Nat := 4983230072969 + 3 ^ 40 * 2965618 * 2
def baseEnd_2965618 : Nat := 1522787471625483239636377

theorem tailTrace_2965618 : CollatzResearch.WordTrace tailWord_2965618 prefixEnd_2965618 1522787471625483239636377 := by
  unfold tailWord_2965618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041243642519987019000377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72109983046719965384001005 27041243642519987019000377)
  ·
    refine ⟨20280932731889990264250283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27041243642519987019000377 20280932731889990264250283)
    ·
      refine ⟨30421399097834985396375425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20280932731889990264250283 30421399097834985396375425)
      ·
        refine ⟨22816049323376239047281569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30421399097834985396375425 22816049323376239047281569)
        ·
          refine ⟨17112036992532179285461177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22816049323376239047281569 17112036992532179285461177)
          ·
            refine ⟨12834027744399134464095883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17112036992532179285461177 12834027744399134464095883)
            ·
              refine ⟨19251041616598701696143825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12834027744399134464095883 19251041616598701696143825)
              ·
                refine ⟨14438281212449026272107869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19251041616598701696143825 14438281212449026272107869)
                ·
                  refine ⟨5414355454668384852040451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14438281212449026272107869 5414355454668384852040451)
                  ·
                    refine ⟨8121533182002577278060677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5414355454668384852040451 8121533182002577278060677)
                    ·
                      refine ⟨1522787471625483239636377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8121533182002577278060677 1522787471625483239636377)
                      ·
                        rfl

theorem cell23_2965618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2965618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965618 prefixEnd_2965618 := by exact prefixLift 2965618
  have htrace : WordTrace (prefixWord ++ tailWord_2965618) baseStart_2965618 baseEnd_2965618 := by
    simpa [prefixWord, tailWord_2965618, baseEnd_2965618] using wordTrace_append hprefix tailTrace_2965618
  have hstable : (prefixWord ++ tailWord_2965618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965618).length < 2 ^ (prefixWord ++ tailWord_2965618).sum := by decide
  have hdescent : baseEnd_2965618 < baseStart_2965618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965628 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_2965628 : Nat := 118140960795 + 2965628 * 2 ^ 59
def prefixEnd_2965628 : Nat := 4983230072969 + 3 ^ 40 * 2965628 * 2
def baseEnd_2965628 : Nat := 507597535477342733503777

theorem tailTrace_2965628 : CollatzResearch.WordTrace tailWord_2965628 prefixEnd_2965628 507597535477342733503777 := by
  unfold tailWord_2965628
  simp only [CollatzResearch.WordTrace]
  refine ⟨54082669650021859891932769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72110226200029146522577025 54082669650021859891932769)
  ·
    refine ⟨40562002237516394918949577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54082669650021859891932769 40562002237516394918949577)
    ·
      refine ⟨30421501678137296189212183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40562002237516394918949577 30421501678137296189212183)
      ·
        refine ⟨45632252517205944283818275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30421501678137296189212183 45632252517205944283818275)
        ·
          refine ⟨68448378775808916425727413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45632252517205944283818275 68448378775808916425727413)
          ·
            refine ⟨6417035510232085914911945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68448378775808916425727413 6417035510232085914911945)
            ·
              refine ⟨4812776632674064436183959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6417035510232085914911945 4812776632674064436183959)
              ·
                refine ⟨7219164949011096654275939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4812776632674064436183959 7219164949011096654275939)
                ·
                  refine ⟨10828747423516644981413909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7219164949011096654275939 10828747423516644981413909)
                  ·
                    refine ⟨507597535477342733503777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10828747423516644981413909 507597535477342733503777)
                    ·
                      rfl

theorem cell23_2965628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_2965628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965628 prefixEnd_2965628 := by exact prefixLift 2965628
  have htrace : WordTrace (prefixWord ++ tailWord_2965628) baseStart_2965628 baseEnd_2965628 := by
    simpa [prefixWord, tailWord_2965628, baseEnd_2965628] using wordTrace_append hprefix tailTrace_2965628
  have hstable : (prefixWord ++ tailWord_2965628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965628).length < 2 ^ (prefixWord ++ tailWord_2965628).sum := by decide
  have hdescent : baseEnd_2965628 < baseStart_2965628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965635 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 5, 2, 2]
def baseStart_2965635 : Nat := 118140960795 + 2965635 * 2 ^ 59
def prefixEnd_2965635 : Nat := 4983230072969 + 3 ^ 40 * 2965635 * 2
def baseEnd_2965635 : Nat := 1522796200796609673123799

theorem tailTrace_2965635 : CollatzResearch.WordTrace tailWord_2965635 prefixEnd_2965635 1522796200796609673123799 := by
  unfold tailWord_2965635
  simp only [CollatzResearch.WordTrace]
  refine ⟨108165594611018359979370359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72110396407345573319580239 108165594611018359979370359)
  ·
    refine ⟨162248391916527539969055539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108165594611018359979370359 162248391916527539969055539)
    ·
      refine ⟨243372587874791309953583309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162248391916527539969055539 243372587874791309953583309)
      ·
        refine ⟨91264720453046741232593741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243372587874791309953583309 91264720453046741232593741)
        ·
          refine ⟨34224270169892527962222653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91264720453046741232593741 34224270169892527962222653)
          ·
            refine ⟨12834101313709697985833495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34224270169892527962222653 12834101313709697985833495)
            ·
              refine ⟨19251151970564546978750243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12834101313709697985833495 19251151970564546978750243)
              ·
                refine ⟨28876727955846820468125365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19251151970564546978750243 28876727955846820468125365)
                ·
                  refine ⟨2707193245860639418886753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28876727955846820468125365 2707193245860639418886753)
                  ·
                    refine ⟨2030394934395479564165065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2707193245860639418886753 2030394934395479564165065)
                    ·
                      refine ⟨1522796200796609673123799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030394934395479564165065 1522796200796609673123799)
                      ·
                        rfl

theorem cell23_2965635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_2965635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965635 prefixEnd_2965635 := by exact prefixLift 2965635
  have htrace : WordTrace (prefixWord ++ tailWord_2965635) baseStart_2965635 baseEnd_2965635 := by
    simpa [prefixWord, tailWord_2965635, baseEnd_2965635] using wordTrace_append hprefix tailTrace_2965635
  have hstable : (prefixWord ++ tailWord_2965635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965635).length < 2 ^ (prefixWord ++ tailWord_2965635).sum := by decide
  have hdescent : baseEnd_2965635 < baseStart_2965635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965658 : List Nat := [3, 1, 1, 5, 2, 1, 10]
def baseStart_2965658 : Nat := 118140960795 + 2965658 * 2 ^ 59
def prefixEnd_2965658 : Nat := 4983230072969 + 3 ^ 40 * 2965658 * 2
def baseEnd_2965658 : Nat := 18800098899403247939953

theorem tailTrace_2965658 : CollatzResearch.WordTrace tailWord_2965658 prefixEnd_2965658 18800098899403247939953 := by
  unfold tailWord_2965658
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041608372483758726864407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72110955659956689938305085 27041608372483758726864407)
  ·
    refine ⟨40562412558725638090296611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27041608372483758726864407 40562412558725638090296611)
    ·
      refine ⟨60843618838088457135444917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40562412558725638090296611 60843618838088457135444917)
      ·
        refine ⟨5704089266070792856447961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60843618838088457135444917 5704089266070792856447961)
        ·
          refine ⟨4278066949553094642335971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704089266070792856447961 4278066949553094642335971)
          ·
            refine ⟨6417100424329641963503957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278066949553094642335971 6417100424329641963503957)
            ·
              refine ⟨18800098899403247939953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6417100424329641963503957 18800098899403247939953)
              ·
                rfl

theorem cell23_2965658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 10].length) (baseStart_2965658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965658 prefixEnd_2965658 := by exact prefixLift 2965658
  have htrace : WordTrace (prefixWord ++ tailWord_2965658) baseStart_2965658 baseEnd_2965658 := by
    simpa [prefixWord, tailWord_2965658, baseEnd_2965658] using wordTrace_append hprefix tailTrace_2965658
  have hstable : (prefixWord ++ tailWord_2965658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965658).length < 2 ^ (prefixWord ++ tailWord_2965658).sum := by decide
  have hdescent : baseEnd_2965658 < baseStart_2965658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965662 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2965662 : Nat := 118140960795 + 2965662 * 2 ^ 59
def prefixEnd_2965662 : Nat := 4983230072969 + 3 ^ 40 * 2965662 * 2
def baseEnd_2965662 : Nat := 507603354924760355828725

theorem tailTrace_2965662 : CollatzResearch.WordTrace tailWord_2965662 prefixEnd_2965662 507603354924760355828725 := by
  unfold tailWord_2965662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520822422740067948825405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72111052921280362393735493 13520822422740067948825405)
  ·
    refine ⟨5070308408527525480809527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13520822422740067948825405 5070308408527525480809527)
    ·
      refine ⟨7605462612791288221214291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070308408527525480809527 7605462612791288221214291)
      ·
        refine ⟨11408193919186932331821437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605462612791288221214291 11408193919186932331821437)
        ·
          refine ⟨4278072719695099624433039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11408193919186932331821437 4278072719695099624433039)
          ·
            refine ⟨6417109079542649436649559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278072719695099624433039 6417109079542649436649559)
            ·
              refine ⟨9625663619313974154974339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417109079542649436649559 9625663619313974154974339)
              ·
                refine ⟨14438495428970961232461509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625663619313974154974339 14438495428970961232461509)
                ·
                  refine ⟨2707217892932055231086533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14438495428970961232461509 2707217892932055231086533)
                  ·
                    refine ⟨507603354924760355828725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707217892932055231086533 507603354924760355828725)
                    ·
                      rfl

theorem cell23_2965662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2965662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965662 prefixEnd_2965662 := by exact prefixLift 2965662
  have htrace : WordTrace (prefixWord ++ tailWord_2965662) baseStart_2965662 baseEnd_2965662 := by
    simpa [prefixWord, tailWord_2965662, baseEnd_2965662] using wordTrace_append hprefix tailTrace_2965662
  have hstable : (prefixWord ++ tailWord_2965662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965662).length < 2 ^ (prefixWord ++ tailWord_2965662).sum := by decide
  have hdescent : baseEnd_2965662 < baseStart_2965662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965692 : List Nat := [2, 2, 2, 3, 4, 1, 2, 7]
def baseStart_2965692 : Nat := 118140960795 + 2965692 * 2 ^ 59
def prefixEnd_2965692 : Nat := 4983230072969 + 3 ^ 40 * 2965692 * 2
def baseEnd_2965692 : Nat := 56400943303478368522631

theorem tailTrace_2965692 : CollatzResearch.WordTrace tailWord_2965692 prefixEnd_2965692 56400943303478368522631 := by
  unfold tailWord_2965692
  simp only [CollatzResearch.WordTrace]
  refine ⟨54083836785905929357097665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72111782381207905809463553 54083836785905929357097665)
  ·
    refine ⟨40562877589429447017823249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54083836785905929357097665 40562877589429447017823249)
    ·
      refine ⟨30422158192072085263367437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40562877589429447017823249 30422158192072085263367437)
      ·
        refine ⟨11408309322027031973762789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30422158192072085263367437 11408309322027031973762789)
        ·
          refine ⟨2139057997880068495080523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11408309322027031973762789 2139057997880068495080523)
          ·
            refine ⟨3208586996820102742620785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139057997880068495080523 3208586996820102742620785)
            ·
              refine ⟨2406440247615077056965589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208586996820102742620785 2406440247615077056965589)
              ·
                refine ⟨56400943303478368522631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2406440247615077056965589 56400943303478368522631)
                ·
                  rfl

theorem cell23_2965692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 7].length) (baseStart_2965692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965692 prefixEnd_2965692 := by exact prefixLift 2965692
  have htrace : WordTrace (prefixWord ++ tailWord_2965692) baseStart_2965692 baseEnd_2965692 := by
    simpa [prefixWord, tailWord_2965692, baseEnd_2965692] using wordTrace_append hprefix tailTrace_2965692
  have hstable : (prefixWord ++ tailWord_2965692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965692).length < 2 ^ (prefixWord ++ tailWord_2965692).sum := by decide
  have hdescent : baseEnd_2965692 < baseStart_2965692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965701 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_2965701 : Nat := 118140960795 + 2965701 * 2 ^ 59
def prefixEnd_2965701 : Nat := 4983230072969 + 3 ^ 40 * 2965701 * 2
def baseEnd_2965701 : Nat := 507610030173268804966165

theorem tailTrace_2965701 : CollatzResearch.WordTrace tailWord_2965701 prefixEnd_2965701 507610030173268804966165 := by
  unfold tailWord_2965701
  simp only [CollatzResearch.WordTrace]
  refine ⟨108168001828779253251272957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72112001219186168834181971 108168001828779253251272957)
  ·
    refine ⟨40563000685792219969227359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108168001828779253251272957 40563000685792219969227359)
    ·
      refine ⟨60844501028688329953841039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40563000685792219969227359 60844501028688329953841039)
      ·
        refine ⟨91266751543032494930761559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60844501028688329953841039 91266751543032494930761559)
        ·
          refine ⟨136900127314548742396142339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91266751543032494930761559 136900127314548742396142339)
          ·
            refine ⟨205350190971823113594213509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136900127314548742396142339 205350190971823113594213509)
            ·
              refine ⟨38503160807216833798915033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205350190971823113594213509 38503160807216833798915033)
              ·
                refine ⟨28877370605412625349186275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38503160807216833798915033 28877370605412625349186275)
                ·
                  refine ⟨43316055908118938023779413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28877370605412625349186275 43316055908118938023779413)
                  ·
                    refine ⟨507610030173268804966165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43316055908118938023779413 507610030173268804966165)
                    ·
                      rfl

theorem cell23_2965701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_2965701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965701 prefixEnd_2965701 := by exact prefixLift 2965701
  have htrace : WordTrace (prefixWord ++ tailWord_2965701) baseStart_2965701 baseEnd_2965701 := by
    simpa [prefixWord, tailWord_2965701, baseEnd_2965701] using wordTrace_append hprefix tailTrace_2965701
  have hstable : (prefixWord ++ tailWord_2965701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965701).length < 2 ^ (prefixWord ++ tailWord_2965701).sum := by decide
  have hdescent : baseEnd_2965701 < baseStart_2965701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965728 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_2965728 : Nat := 118140960795 + 2965728 * 2 ^ 59
def prefixEnd_2965728 : Nat := 4983230072969 + 3 ^ 40 * 2965728 * 2
def baseEnd_2965728 : Nat := 1522843954497477809260871

theorem tailTrace_2965728 : CollatzResearch.WordTrace tailWord_2965728 prefixEnd_2965728 1522843954497477809260871 := by
  unfold tailWord_2965728
  simp only [CollatzResearch.WordTrace]
  refine ⟨54084493299840718431252919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72112657733120957908337225 54084493299840718431252919)
  ·
    refine ⟨81126739949761077646879379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54084493299840718431252919 81126739949761077646879379)
    ·
      refine ⟨121690109924641616470319069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81126739949761077646879379 121690109924641616470319069)
      ·
        refine ⟨45633791221740606176369651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121690109924641616470319069 45633791221740606176369651)
        ·
          refine ⟨68450686832610909264554477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45633791221740606176369651 68450686832610909264554477)
          ·
            refine ⟨25669007562229090974207929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68450686832610909264554477 25669007562229090974207929)
            ·
              refine ⟨19251755671671818230655947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25669007562229090974207929 19251755671671818230655947)
              ·
                refine ⟨28877633507507727345983921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19251755671671818230655947 28877633507507727345983921)
                ·
                  refine ⟨21658225130630795509487941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28877633507507727345983921 21658225130630795509487941)
                  ·
                    refine ⟨4060917211993274158028989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21658225130630795509487941 4060917211993274158028989)
                    ·
                      refine ⟨1522843954497477809260871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4060917211993274158028989 1522843954497477809260871)
                      ·
                        rfl

theorem cell23_2965728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_2965728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965728 prefixEnd_2965728 := by exact prefixLift 2965728
  have htrace : WordTrace (prefixWord ++ tailWord_2965728) baseStart_2965728 baseEnd_2965728 := by
    simpa [prefixWord, tailWord_2965728, baseEnd_2965728] using wordTrace_append hprefix tailTrace_2965728
  have hstable : (prefixWord ++ tailWord_2965728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965728).length < 2 ^ (prefixWord ++ tailWord_2965728).sum := by decide
  have hdescent : baseEnd_2965728 < baseStart_2965728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965730 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2965730 : Nat := 118140960795 + 2965730 * 2 ^ 59
def prefixEnd_2965730 : Nat := 4983230072969 + 3 ^ 40 * 2965730 * 2
def baseEnd_2965730 : Nat := 507614993819595600478621

theorem tailTrace_2965730 : CollatzResearch.WordTrace tailWord_2965730 prefixEnd_2965730 507614993819595600478621 := by
  unfold tailWord_2965730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27042264886418547801019661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72112706363782794136052429 27042264886418547801019661)
  ·
    refine ⟨10140849332406955425382373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27042264886418547801019661 10140849332406955425382373)
    ·
      refine ⟨1901409249826304142259195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10140849332406955425382373 1901409249826304142259195)
      ·
        refine ⟨2852113874739456213388793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901409249826304142259195 2852113874739456213388793)
        ·
          refine ⟨2139085406054592160041595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852113874739456213388793 2139085406054592160041595)
          ·
            refine ⟨3208628109081888240062393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139085406054592160041595 3208628109081888240062393)
            ·
              refine ⟨2406471081811416180046795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208628109081888240062393 2406471081811416180046795)
              ·
                refine ⟨3609706622717124270070193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406471081811416180046795 3609706622717124270070193)
                ·
                  refine ⟨2707279967037843202552645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3609706622717124270070193 2707279967037843202552645)
                  ·
                    refine ⟨507614993819595600478621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707279967037843202552645 507614993819595600478621)
                    ·
                      rfl

theorem cell23_2965730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2965730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965730 prefixEnd_2965730 := by exact prefixLift 2965730
  have htrace : WordTrace (prefixWord ++ tailWord_2965730) baseStart_2965730 baseEnd_2965730 := by
    simpa [prefixWord, tailWord_2965730, baseEnd_2965730] using wordTrace_append hprefix tailTrace_2965730
  have hstable : (prefixWord ++ tailWord_2965730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965730).length < 2 ^ (prefixWord ++ tailWord_2965730).sum := by decide
  have hdescent : baseEnd_2965730 < baseStart_2965730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965738 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2965738 : Nat := 118140960795 + 2965738 * 2 ^ 59
def prefixEnd_2965738 : Nat := 4983230072969 + 3 ^ 40 * 2965738 * 2
def baseEnd_2965738 : Nat := 1522849089304022770135825

theorem tailTrace_2965738 : CollatzResearch.WordTrace tailWord_2965738 prefixEnd_2965738 1522849089304022770135825 := by
  unfold tailWord_2965738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27042337832411302142592467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72112900886430139046913245 27042337832411302142592467)
  ·
    refine ⟨40563506748616953213888701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27042337832411302142592467 40563506748616953213888701)
    ·
      refine ⟨15211315030731357455208263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40563506748616953213888701 15211315030731357455208263)
      ·
        refine ⟨22816972546097036182812395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15211315030731357455208263 22816972546097036182812395)
        ·
          refine ⟨34225458819145554274218593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22816972546097036182812395 34225458819145554274218593)
          ·
            refine ⟨25669094114359165705663945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34225458819145554274218593 25669094114359165705663945)
            ·
              refine ⟨19251820585769374279247959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25669094114359165705663945 19251820585769374279247959)
              ·
                refine ⟨28877730878654061418871939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19251820585769374279247959 28877730878654061418871939)
                ·
                  refine ⟨43316596317981092128307909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28877730878654061418871939 43316596317981092128307909)
                  ·
                    refine ⟨8121861809621454774057733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43316596317981092128307909 8121861809621454774057733)
                    ·
                      refine ⟨1522849089304022770135825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8121861809621454774057733 1522849089304022770135825)
                      ·
                        rfl

theorem cell23_2965738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2965738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965738 prefixEnd_2965738 := by exact prefixLift 2965738
  have htrace : WordTrace (prefixWord ++ tailWord_2965738) baseStart_2965738 baseEnd_2965738 := by
    simpa [prefixWord, tailWord_2965738, baseEnd_2965738] using wordTrace_append hprefix tailTrace_2965738
  have hstable : (prefixWord ++ tailWord_2965738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965738).length < 2 ^ (prefixWord ++ tailWord_2965738).sum := by decide
  have hdescent : baseEnd_2965738 < baseStart_2965738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965799 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 7]
def baseStart_2965799 : Nat := 118140960795 + 2965799 * 2 ^ 59
def prefixEnd_2965799 : Nat := 4983230072969 + 3 ^ 40 * 2965799 * 2
def baseEnd_2965799 : Nat := 169208934624883003497005

theorem tailTrace_2965799 : CollatzResearch.WordTrace tailWord_2965799 prefixEnd_2965799 169208934624883003497005 := by
  unfold tailWord_2965799
  simp only [CollatzResearch.WordTrace]
  refine ⟨108171576182424215988340451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72114384121616143992226967 108171576182424215988340451)
  ·
    refine ⟨162257364273636323982510677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108171576182424215988340451 162257364273636323982510677)
    ·
      refine ⟨1901453487581675671670047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 162257364273636323982510677 1901453487581675671670047)
      ·
        refine ⟨2852180231372513507505071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901453487581675671670047 2852180231372513507505071)
        ·
          refine ⟨4278270347058770261257607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852180231372513507505071 4278270347058770261257607)
          ·
            refine ⟨6417405520588155391886411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278270347058770261257607 6417405520588155391886411)
            ·
              refine ⟨9626108280882233087829617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417405520588155391886411 9626108280882233087829617)
              ·
                refine ⟨7219581210661674815872213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9626108280882233087829617 7219581210661674815872213)
                ·
                  refine ⟨169208934624883003497005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7219581210661674815872213 169208934624883003497005)
                  ·
                    rfl

theorem cell23_2965799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 7].length) (baseStart_2965799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965799 prefixEnd_2965799 := by exact prefixLift 2965799
  have htrace : WordTrace (prefixWord ++ tailWord_2965799) baseStart_2965799 baseEnd_2965799 := by
    simpa [prefixWord, tailWord_2965799, baseEnd_2965799] using wordTrace_append hprefix tailTrace_2965799
  have hstable : (prefixWord ++ tailWord_2965799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965799).length < 2 ^ (prefixWord ++ tailWord_2965799).sum := by decide
  have hdescent : baseEnd_2965799 < baseStart_2965799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965812 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2965812 : Nat := 118140960795 + 2965812 * 2 ^ 59
def prefixEnd_2965812 : Nat := 4983230072969 + 3 ^ 40 * 2965812 * 2
def baseEnd_2965812 : Nat := 507629028957485160203495

theorem tailTrace_2965812 : CollatzResearch.WordTrace tailWord_2965812 prefixEnd_2965812 507629028957485160203495 := by
  unfold tailWord_2965812
  simp only [CollatzResearch.WordTrace]
  refine ⟨54086025165688559604281845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72114700220918079472375793 54086025165688559604281845)
  ·
    refine ⟨5070564859283302462901423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54086025165688559604281845 5070564859283302462901423)
    ·
      refine ⟨7605847288924953694352135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070564859283302462901423 7605847288924953694352135)
      ·
        refine ⟨11408770933387430541528203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605847288924953694352135 11408770933387430541528203)
        ·
          refine ⟨17113156400081145812292305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11408770933387430541528203 17113156400081145812292305)
          ·
            refine ⟨12834867300060859359219229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17113156400081145812292305 12834867300060859359219229)
            ·
              refine ⟨4813075237522822259707211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12834867300060859359219229 4813075237522822259707211)
              ·
                refine ⟨7219612856284233389560817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813075237522822259707211 7219612856284233389560817)
                ·
                  refine ⟨5414709642213175042170613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7219612856284233389560817 5414709642213175042170613)
                  ·
                    refine ⟨507629028957485160203495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5414709642213175042170613 507629028957485160203495)
                    ·
                      rfl

theorem cell23_2965812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2965812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965812 prefixEnd_2965812 := by exact prefixLift 2965812
  have htrace : WordTrace (prefixWord ++ tailWord_2965812) baseStart_2965812 baseEnd_2965812 := by
    simpa [prefixWord, tailWord_2965812, baseEnd_2965812] using wordTrace_append hprefix tailTrace_2965812
  have hstable : (prefixWord ++ tailWord_2965812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965812).length < 2 ^ (prefixWord ++ tailWord_2965812).sum := by decide
  have hdescent : baseEnd_2965812 < baseStart_2965812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965899 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 3]
def baseStart_2965899 : Nat := 118140960795 + 2965899 * 2 ^ 59
def prefixEnd_2965899 : Nat := 4983230072969 + 3 ^ 40 * 2965899 * 2
def baseEnd_2965899 : Nat := 1522931759689396640222585

theorem tailTrace_2965899 : CollatzResearch.WordTrace tailWord_2965899 prefixEnd_2965899 1522931759689396640222585 := by
  unfold tailWord_2965899
  simp only [CollatzResearch.WordTrace]
  refine ⟨108175223482061933066980751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72116815654707955377987167 108175223482061933066980751)
  ·
    refine ⟨162262835223092899600471127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108175223482061933066980751 162262835223092899600471127)
    ·
      refine ⟨243394252834639349400706691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162262835223092899600471127 243394252834639349400706691)
      ·
        refine ⟨365091379251959024101060037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243394252834639349400706691 365091379251959024101060037)
        ·
          refine ⟨68454633609742317018948757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365091379251959024101060037 68454633609742317018948757)
          ·
            refine ⟨3208810950456671110263223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68454633609742317018948757 3208810950456671110263223)
            ·
              refine ⟨4813216425685006665394835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208810950456671110263223 4813216425685006665394835)
              ·
                refine ⟨7219824638527509998092253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813216425685006665394835 7219824638527509998092253)
                ·
                  refine ⟨2707434239447816249284595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7219824638527509998092253 2707434239447816249284595)
                  ·
                    refine ⟨4061151359171724373926893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707434239447816249284595 4061151359171724373926893)
                    ·
                      refine ⟨1522931759689396640222585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061151359171724373926893 1522931759689396640222585)
                      ·
                        rfl

theorem cell23_2965899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 3].length) (baseStart_2965899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965899 prefixEnd_2965899 := by exact prefixLift 2965899
  have htrace : WordTrace (prefixWord ++ tailWord_2965899) baseStart_2965899 baseEnd_2965899 := by
    simpa [prefixWord, tailWord_2965899, baseEnd_2965899] using wordTrace_append hprefix tailTrace_2965899
  have hstable : (prefixWord ++ tailWord_2965899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965899).length < 2 ^ (prefixWord ++ tailWord_2965899).sum := by decide
  have hdescent : baseEnd_2965899 < baseStart_2965899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965922 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2965922 : Nat := 118140960795 + 2965922 * 2 ^ 59
def prefixEnd_2965922 : Nat := 4983230072969 + 3 ^ 40 * 2965922 * 2
def baseEnd_2965922 : Nat := 1522943569744450050234979

theorem tailTrace_2965922 : CollatzResearch.WordTrace tailWord_2965922 prefixEnd_2965922 1522943569744450050234979 := by
  unfold tailWord_2965922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27044015590244651998767005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72117374907319071996712013 27044015590244651998767005)
  ·
    refine ⟨10141505846341744499537627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27044015590244651998767005 10141505846341744499537627)
    ·
      refine ⟨15212258769512616749306441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10141505846341744499537627 15212258769512616749306441)
      ·
        refine ⟨11409194077134462561979831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15212258769512616749306441 11409194077134462561979831)
        ·
          refine ⟨17113791115701693842969747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11409194077134462561979831 17113791115701693842969747)
          ·
            refine ⟨25670686673552540764454621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17113791115701693842969747 25670686673552540764454621)
            ·
              refine ⟨9626507502582202786670483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25670686673552540764454621 9626507502582202786670483)
              ·
                refine ⟨14439761253873304180005725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9626507502582202786670483 14439761253873304180005725)
                ·
                  refine ⟨5414910470202489067502147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14439761253873304180005725 5414910470202489067502147)
                  ·
                    refine ⟨8122365705303733601253221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5414910470202489067502147 8122365705303733601253221)
                    ·
                      refine ⟨1522943569744450050234979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8122365705303733601253221 1522943569744450050234979)
                      ·
                        rfl

theorem cell23_2965922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2965922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965922 prefixEnd_2965922 := by exact prefixLift 2965922
  have htrace : WordTrace (prefixWord ++ tailWord_2965922) baseStart_2965922 baseEnd_2965922 := by
    simpa [prefixWord, tailWord_2965922, baseEnd_2965922] using wordTrace_append hprefix tailTrace_2965922
  have hstable : (prefixWord ++ tailWord_2965922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965922).length < 2 ^ (prefixWord ++ tailWord_2965922).sum := by decide
  have hdescent : baseEnd_2965922 < baseStart_2965922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965949 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2965949 : Nat := 118140960795 + 2965949 * 2 ^ 59
def prefixEnd_2965949 : Nat := 4983230072969 + 3 ^ 40 * 2965949 * 2
def baseEnd_2965949 : Nat := 507652477907373814865785

theorem tailTrace_2965949 : CollatzResearch.WordTrace tailWord_2965949 prefixEnd_2965949 507652477907373814865785 := by
  unfold tailWord_2965949
  simp only [CollatzResearch.WordTrace]
  refine ⟨108177047131880791606300901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72118031421253861070867267 108177047131880791606300901)
  ·
    refine ⟨20283196337227648426181419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108177047131880791606300901 20283196337227648426181419)
    ·
      refine ⟨30424794505841472639272129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283196337227648426181419 30424794505841472639272129)
      ·
        refine ⟨22818595879381104479454097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30424794505841472639272129 22818595879381104479454097)
        ·
          refine ⟨17113946909535828359590573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22818595879381104479454097 17113946909535828359590573)
          ·
            refine ⟨6417730091075935634846465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17113946909535828359590573 6417730091075935634846465)
            ·
              refine ⟨4813297568306951726134849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6417730091075935634846465 4813297568306951726134849)
              ·
                refine ⟨3609973176230213794601137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813297568306951726134849 3609973176230213794601137)
                ·
                  refine ⟨2707479882172660345950853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3609973176230213794601137 2707479882172660345950853)
                  ·
                    refine ⟨507652477907373814865785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707479882172660345950853 507652477907373814865785)
                    ·
                      rfl

theorem cell23_2965949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2965949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965949 prefixEnd_2965949 := by exact prefixLift 2965949
  have htrace : WordTrace (prefixWord ++ tailWord_2965949) baseStart_2965949 baseEnd_2965949 := by
    simpa [prefixWord, tailWord_2965949, baseEnd_2965949] using wordTrace_append hprefix tailTrace_2965949
  have hstable : (prefixWord ++ tailWord_2965949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965949).length < 2 ^ (prefixWord ++ tailWord_2965949).sum := by decide
  have hdescent : baseEnd_2965949 < baseStart_2965949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965955 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 3]
def baseStart_2965955 : Nat := 118140960795 + 2965955 * 2 ^ 59
def prefixEnd_2965955 : Nat := 4983230072969 + 3 ^ 40 * 2965955 * 2
def baseEnd_2965955 : Nat := 1522960514606048421122327

theorem tailTrace_2965955 : CollatzResearch.WordTrace tailWord_2965955 prefixEnd_2965955 1522960514606048421122327 := by
  unfold tailWord_2965955
  simp only [CollatzResearch.WordTrace]
  refine ⟨108177265969859054631019319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72118177313239369754012879 108177265969859054631019319)
  ·
    refine ⟨162265898954788581946528979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108177265969859054631019319 162265898954788581946528979)
    ·
      refine ⟨243398848432182872919793469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162265898954788581946528979 243398848432182872919793469)
      ·
        refine ⟨91274568162068577344922551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243398848432182872919793469 91274568162068577344922551)
        ·
          refine ⟨136911852243102866017383827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91274568162068577344922551 136911852243102866017383827)
          ·
            refine ⟨205367778364654299026075741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136911852243102866017383827 205367778364654299026075741)
            ·
              refine ⟨77012916886745362134778403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205367778364654299026075741 77012916886745362134778403)
              ·
                refine ⟨115519375330118043202167605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77012916886745362134778403 115519375330118043202167605)
                ·
                  refine ⟨10829941437198566550203213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115519375330118043202167605 10829941437198566550203213)
                  ·
                    refine ⟨4061228038949462456326205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10829941437198566550203213 4061228038949462456326205)
                    ·
                      refine ⟨1522960514606048421122327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061228038949462456326205 1522960514606048421122327)
                      ·
                        rfl

theorem cell23_2965955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_2965955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965955 prefixEnd_2965955 := by exact prefixLift 2965955
  have htrace : WordTrace (prefixWord ++ tailWord_2965955) baseStart_2965955 baseEnd_2965955 := by
    simpa [prefixWord, tailWord_2965955, baseEnd_2965955] using wordTrace_append hprefix tailTrace_2965955
  have hstable : (prefixWord ++ tailWord_2965955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965955).length < 2 ^ (prefixWord ++ tailWord_2965955).sum := by decide
  have hdescent : baseEnd_2965955 < baseStart_2965955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965985 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2965985 : Nat := 118140960795 + 2965985 * 2 ^ 59
def prefixEnd_2965985 : Nat := 4983230072969 + 3 ^ 40 * 2965985 * 2
def baseEnd_2965985 : Nat := 1522975919025683303747189

theorem tailTrace_2965985 : CollatzResearch.WordTrace tailWord_2965985 prefixEnd_2965985 1522975919025683303747189 := by
  unfold tailWord_2965985
  simp only [CollatzResearch.WordTrace]
  refine ⟨108178360159750369754611409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72118906773166913169740939 108178360159750369754611409)
  ·
    refine ⟨81133770119812777315958557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108178360159750369754611409 81133770119812777315958557)
    ·
      refine ⟨30425163794929791493484459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81133770119812777315958557 30425163794929791493484459)
      ·
        refine ⟨45637745692394687240226689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30425163794929791493484459 45637745692394687240226689)
        ·
          refine ⟨34228309269296015430170017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45637745692394687240226689 34228309269296015430170017)
          ·
            refine ⟨25671231951972011572627513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34228309269296015430170017 25671231951972011572627513)
            ·
              refine ⟨19253423963979008679470635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25671231951972011572627513 19253423963979008679470635)
              ·
                refine ⟨28880135945968513019205953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19253423963979008679470635 28880135945968513019205953)
                ·
                  refine ⟨21660101959476384764404465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28880135945968513019205953 21660101959476384764404465)
                  ·
                    refine ⟨16245076469607288573303349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21660101959476384764404465 16245076469607288573303349)
                    ·
                      refine ⟨1522975919025683303747189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16245076469607288573303349 1522975919025683303747189)
                      ·
                        rfl

theorem cell23_2965985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2965985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2965985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2965985 prefixEnd_2965985 := by exact prefixLift 2965985
  have htrace : WordTrace (prefixWord ++ tailWord_2965985) baseStart_2965985 baseEnd_2965985 := by
    simpa [prefixWord, tailWord_2965985, baseEnd_2965985] using wordTrace_append hprefix tailTrace_2965985
  have hstable : (prefixWord ++ tailWord_2965985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965985).length < 2 ^ (prefixWord ++ tailWord_2965985).sum := by decide
  have hdescent : baseEnd_2965985 < baseStart_2965985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966023 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2966023 : Nat := 118140960795 + 2966023 * 2 ^ 59
def prefixEnd_2966023 : Nat := 4983230072969 + 3 ^ 40 * 2966023 * 2
def baseEnd_2966023 : Nat := 1522995431290554155072015

theorem tailTrace_2966023 : CollatzResearch.WordTrace tailWord_2966023 prefixEnd_2966023 1522995431290554155072015 := by
  unfold tailWord_2966023
  simp only [CollatzResearch.WordTrace]
  refine ⟨108179746133612702244494723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72119830755741801496329815 108179746133612702244494723)
  ·
    refine ⟨162269619200419053366742085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108179746133612702244494723 162269619200419053366742085)
    ·
      refine ⟨30425553600078572506264141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162269619200419053366742085 30425553600078572506264141)
      ·
        refine ⟨11409582600029464689849053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30425553600078572506264141 11409582600029464689849053)
        ·
          refine ⟨4278593475011049258693395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11409582600029464689849053 4278593475011049258693395)
          ·
            refine ⟨6417890212516573888040093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278593475011049258693395 6417890212516573888040093)
            ·
              refine ⟨2406708829693715208015035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6417890212516573888040093 2406708829693715208015035)
              ·
                refine ⟨3610063244540572812022553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406708829693715208015035 3610063244540572812022553)
                ·
                  refine ⟨2707547433405429609016915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610063244540572812022553 2707547433405429609016915)
                  ·
                    refine ⟨4061321150108144413525373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707547433405429609016915 4061321150108144413525373)
                    ·
                      refine ⟨1522995431290554155072015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061321150108144413525373 1522995431290554155072015)
                      ·
                        rfl

theorem cell23_2966023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2966023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966023 prefixEnd_2966023 := by exact prefixLift 2966023
  have htrace : WordTrace (prefixWord ++ tailWord_2966023) baseStart_2966023 baseEnd_2966023 := by
    simpa [prefixWord, tailWord_2966023, baseEnd_2966023] using wordTrace_append hprefix tailTrace_2966023
  have hstable : (prefixWord ++ tailWord_2966023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966023).length < 2 ^ (prefixWord ++ tailWord_2966023).sum := by decide
  have hdescent : baseEnd_2966023 < baseStart_2966023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966025 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_2966025 : Nat := 118140960795 + 2966025 * 2 ^ 59
def prefixEnd_2966025 : Nat := 4983230072969 + 3 ^ 40 * 2966025 * 2
def baseEnd_2966025 : Nat := 1522996458251863147247005

theorem tailTrace_2966025 : CollatzResearch.WordTrace tailWord_2966025 prefixEnd_2966025 1522996458251863147247005 := by
  unfold tailWord_2966025
  simp only [CollatzResearch.WordTrace]
  refine ⟨108179819079605456586067529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72119879386403637724045019 108179819079605456586067529)
  ·
    refine ⟨81134864309704092439550647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108179819079605456586067529 81134864309704092439550647)
    ·
      refine ⟨121702296464556138659325971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81134864309704092439550647 121702296464556138659325971)
      ·
        refine ⟨182553444696834207988988957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121702296464556138659325971 182553444696834207988988957)
        ·
          refine ⟨68457541761312827995870859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182553444696834207988988957 68457541761312827995870859)
          ·
            refine ⟨102686312641969241993806289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68457541761312827995870859 102686312641969241993806289)
            ·
              refine ⟨77014734481476931495354717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102686312641969241993806289 77014734481476931495354717)
              ·
                refine ⟨28880525430553849310758019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77014734481476931495354717 28880525430553849310758019)
                ·
                  refine ⟨43320788145830773966137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28880525430553849310758019 43320788145830773966137029)
                  ·
                    refine ⟨8122647777343270118650693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43320788145830773966137029 8122647777343270118650693)
                    ·
                      refine ⟨1522996458251863147247005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8122647777343270118650693 1522996458251863147247005)
                      ·
                        rfl

theorem cell23_2966025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_2966025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966025 prefixEnd_2966025 := by exact prefixLift 2966025
  have htrace : WordTrace (prefixWord ++ tailWord_2966025) baseStart_2966025 baseEnd_2966025 := by
    simpa [prefixWord, tailWord_2966025, baseEnd_2966025] using wordTrace_append hprefix tailTrace_2966025
  have hstable : (prefixWord ++ tailWord_2966025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966025).length < 2 ^ (prefixWord ++ tailWord_2966025).sum := by decide
  have hdescent : baseEnd_2966025 < baseStart_2966025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966035 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 7]
def baseStart_2966035 : Nat := 118140960795 + 2966035 * 2 ^ 59
def prefixEnd_2966035 : Nat := 4983230072969 + 3 ^ 40 * 2966035 * 2
def baseEnd_2966035 : Nat := 169222399228712012013551

theorem tailTrace_2966035 : CollatzResearch.WordTrace tailWord_2966035 prefixEnd_2966035 169222399228712012013551 := by
  unfold tailWord_2966035
  simp only [CollatzResearch.WordTrace]
  refine ⟨108180183809569228293931559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72120122539712818862621039 108180183809569228293931559)
  ·
    refine ⟨162270275714353842440897339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108180183809569228293931559 162270275714353842440897339)
    ·
      refine ⟨243405413571530763661346009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162270275714353842440897339 243405413571530763661346009)
      ·
        refine ⟨182554060178648072746009507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243405413571530763661346009 182554060178648072746009507)
        ·
          refine ⟨273831090267972109119014261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182554060178648072746009507 273831090267972109119014261)
          ·
            refine ⟨25671664712622385229907587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273831090267972109119014261 25671664712622385229907587)
            ·
              refine ⟨38507497068933577844861381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25671664712622385229907587 38507497068933577844861381)
              ·
                refine ⟨7220155700425045845911509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38507497068933577844861381 7220155700425045845911509)
                ·
                  refine ⟨169222399228712012013551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7220155700425045845911509 169222399228712012013551)
                  ·
                    rfl

theorem cell23_2966035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 7].length) (baseStart_2966035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966035 prefixEnd_2966035 := by exact prefixLift 2966035
  have htrace : WordTrace (prefixWord ++ tailWord_2966035) baseStart_2966035 baseEnd_2966035 := by
    simpa [prefixWord, tailWord_2966035, baseEnd_2966035] using wordTrace_append hprefix tailTrace_2966035
  have hstable : (prefixWord ++ tailWord_2966035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966035).length < 2 ^ (prefixWord ++ tailWord_2966035).sum := by decide
  have hdescent : baseEnd_2966035 < baseStart_2966035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966084 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2966084 : Nat := 118140960795 + 2966084 * 2 ^ 59
def prefixEnd_2966084 : Nat := 4983230072969 + 3 ^ 40 * 2966084 * 2
def baseEnd_2966084 : Nat := 1523026753610478416409235

theorem tailTrace_2966084 : CollatzResearch.WordTrace tailWord_2966084 prefixEnd_2966084 1523026753610478416409235 := by
  unfold tailWord_2966084
  simp only [CollatzResearch.WordTrace]
  refine ⟨54090985493195854831232653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72121313990927806441643537 54090985493195854831232653)
  ·
    refine ⟨20284119559948445561712245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54090985493195854831232653 20284119559948445561712245)
    ·
      refine ⟨1901636208745166771410523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20284119559948445561712245 1901636208745166771410523)
      ·
        refine ⟨2852454313117750157115785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901636208745166771410523 2852454313117750157115785)
        ·
          refine ⟨2139340734838312617836839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852454313117750157115785 2139340734838312617836839)
          ·
            refine ⟨3209011102257468926755259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139340734838312617836839 3209011102257468926755259)
            ·
              refine ⟨4813516653386203390132889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209011102257468926755259 4813516653386203390132889)
              ·
                refine ⟨3610137490039652542599667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813516653386203390132889 3610137490039652542599667)
                ·
                  refine ⟨5415206235059478813899501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610137490039652542599667 5415206235059478813899501)
                  ·
                    refine ⟨2030702338147304555212313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5415206235059478813899501 2030702338147304555212313)
                    ·
                      refine ⟨1523026753610478416409235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030702338147304555212313 1523026753610478416409235)
                      ·
                        rfl

theorem cell23_2966084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2966084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966084 prefixEnd_2966084 := by exact prefixLift 2966084
  have htrace : WordTrace (prefixWord ++ tailWord_2966084) baseStart_2966084 baseEnd_2966084 := by
    simpa [prefixWord, tailWord_2966084, baseEnd_2966084] using wordTrace_append hprefix tailTrace_2966084
  have hstable : (prefixWord ++ tailWord_2966084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966084).length < 2 ^ (prefixWord ++ tailWord_2966084).sum := by decide
  have hdescent : baseEnd_2966084 < baseStart_2966084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966095 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 8]
def baseStart_2966095 : Nat := 118140960795 + 2966095 * 2 ^ 59
def prefixEnd_2966095 : Nat := 4983230072969 + 3 ^ 40 * 2966095 * 2
def baseEnd_2966095 : Nat := 507677467299225957790561

theorem tailTrace_2966095 : CollatzResearch.WordTrace tailWord_2966095 prefixEnd_2966095 507677467299225957790561 := by
  unfold tailWord_2966095
  simp only [CollatzResearch.WordTrace]
  refine ⟨108182372189351858541115739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72121581459567905694077159 108182372189351858541115739)
  ·
    refine ⟨162273558284027787811673609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108182372189351858541115739 162273558284027787811673609)
    ·
      refine ⟨121705168713020840858755207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162273558284027787811673609 121705168713020840858755207)
      ·
        refine ⟨182557753069531261288132811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121705168713020840858755207 182557753069531261288132811)
        ·
          refine ⟨273836629604296891932199217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182557753069531261288132811 273836629604296891932199217)
          ·
            refine ⟨205377472203222668949149413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273836629604296891932199217 205377472203222668949149413)
            ·
              refine ⟨38508276038104250427965515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205377472203222668949149413 38508276038104250427965515)
              ·
                refine ⟨57762414057156375641948273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38508276038104250427965515 57762414057156375641948273)
                ·
                  refine ⟨43321810542867281731461205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57762414057156375641948273 43321810542867281731461205)
                  ·
                    refine ⟨507677467299225957790561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43321810542867281731461205 507677467299225957790561)
                    ·
                      rfl

theorem cell23_2966095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_2966095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966095 prefixEnd_2966095 := by exact prefixLift 2966095
  have htrace : WordTrace (prefixWord ++ tailWord_2966095) baseStart_2966095 baseEnd_2966095 := by
    simpa [prefixWord, tailWord_2966095, baseEnd_2966095] using wordTrace_append hprefix tailTrace_2966095
  have hstable : (prefixWord ++ tailWord_2966095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966095).length < 2 ^ (prefixWord ++ tailWord_2966095).sum := by decide
  have hdescent : baseEnd_2966095 < baseStart_2966095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966105 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2966105 : Nat := 118140960795 + 2966105 * 2 ^ 59
def prefixEnd_2966105 : Nat := 4983230072969 + 3 ^ 40 * 2966105 * 2
def baseEnd_2966105 : Nat := 1523037536704222834246637

theorem tailTrace_2966105 : CollatzResearch.WordTrace tailWord_2966105 prefixEnd_2966105 1523037536704222834246637 := by
  unfold tailWord_2966105
  simp only [CollatzResearch.WordTrace]
  refine ⟨108182736919315630248979769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72121824612877086832653179 108182736919315630248979769)
  ·
    refine ⟨81137052689486722686734827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108182736919315630248979769 81137052689486722686734827)
    ·
      refine ⟨121705579034230084030102241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81137052689486722686734827 121705579034230084030102241)
      ·
        refine ⟨91279184275672563022576681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121705579034230084030102241 91279184275672563022576681)
        ·
          refine ⟨68459388206754422266932511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91279184275672563022576681 68459388206754422266932511)
          ·
            refine ⟨102689082310131633400398767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68459388206754422266932511 102689082310131633400398767)
            ·
              refine ⟨154033623465197450100598151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102689082310131633400398767 154033623465197450100598151)
              ·
                refine ⟨231050435197796175150897227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154033623465197450100598151 231050435197796175150897227)
                ·
                  refine ⟨346575652796694262726345841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231050435197796175150897227 346575652796694262726345841)
                  ·
                    refine ⟨259931739597520697044759381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346575652796694262726345841 259931739597520697044759381)
                    ·
                      refine ⟨1523037536704222834246637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 259931739597520697044759381 1523037536704222834246637)
                      ·
                        rfl

theorem cell23_2966105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2966105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966105 prefixEnd_2966105 := by exact prefixLift 2966105
  have htrace : WordTrace (prefixWord ++ tailWord_2966105) baseStart_2966105 baseEnd_2966105 := by
    simpa [prefixWord, tailWord_2966105, baseEnd_2966105] using wordTrace_append hprefix tailTrace_2966105
  have hstable : (prefixWord ++ tailWord_2966105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966105).length < 2 ^ (prefixWord ++ tailWord_2966105).sum := by decide
  have hdescent : baseEnd_2966105 < baseStart_2966105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966119 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_2966119 : Nat := 118140960795 + 2966119 * 2 ^ 59
def prefixEnd_2966119 : Nat := 4983230072969 + 3 ^ 40 * 2966119 * 2
def baseEnd_2966119 : Nat := 1523044725433385779471573

theorem tailTrace_2966119 : CollatzResearch.WordTrace tailWord_2966119 prefixEnd_2966119 1523044725433385779471573 := by
  unfold tailWord_2966119
  simp only [CollatzResearch.WordTrace]
  refine ⟨108183247541264910639989411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72122165027509940426659607 108183247541264910639989411)
  ·
    refine ⟨162274871311897365959984117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108183247541264910639989411 162274871311897365959984117)
    ·
      refine ⟨15213269185490378058748511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162274871311897365959984117 15213269185490378058748511)
      ·
        refine ⟨22819903778235567088122767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15213269185490378058748511 22819903778235567088122767)
        ·
          refine ⟨34229855667353350632184151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22819903778235567088122767 34229855667353350632184151)
          ·
            refine ⟨51344783501030025948276227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34229855667353350632184151 51344783501030025948276227)
            ·
              refine ⟨77017175251545038922414341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51344783501030025948276227 77017175251545038922414341)
              ·
                refine ⟨14440720359664694797952689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77017175251545038922414341 14440720359664694797952689)
                ·
                  refine ⟨10830540269748521098464517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14440720359664694797952689 10830540269748521098464517)
                  ·
                    refine ⟨2030726300577847705962097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10830540269748521098464517 2030726300577847705962097)
                    ·
                      refine ⟨1523044725433385779471573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030726300577847705962097 1523044725433385779471573)
                      ·
                        rfl

theorem cell23_2966119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_2966119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966119 prefixEnd_2966119 := by exact prefixLift 2966119
  have htrace : WordTrace (prefixWord ++ tailWord_2966119) baseStart_2966119 baseEnd_2966119 := by
    simpa [prefixWord, tailWord_2966119, baseEnd_2966119] using wordTrace_append hprefix tailTrace_2966119
  have hstable : (prefixWord ++ tailWord_2966119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966119).length < 2 ^ (prefixWord ++ tailWord_2966119).sum := by decide
  have hdescent : baseEnd_2966119 < baseStart_2966119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966120 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 5]
def baseStart_2966120 : Nat := 118140960795 + 2966120 * 2 ^ 59
def prefixEnd_2966120 : Nat := 4983230072969 + 3 ^ 40 * 2966120 * 2
def baseEnd_2966120 : Nat := 169227248768226697284341

theorem tailTrace_2966120 : CollatzResearch.WordTrace tailWord_2966120 prefixEnd_2966120 169227248768226697284341 := by
  unfold tailWord_2966120
  simp only [CollatzResearch.WordTrace]
  refine ⟨54091642007130643905387907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72122189342840858540517209 54091642007130643905387907)
  ·
    refine ⟨81137463010695965858081861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54091642007130643905387907 81137463010695965858081861)
    ·
      refine ⟨15213274314505493598390349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81137463010695965858081861 15213274314505493598390349)
      ·
        refine ⟨5704977867939560099396381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15213274314505493598390349 5704977867939560099396381)
        ·
          refine ⟨2139366700477335037273643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5704977867939560099396381 2139366700477335037273643)
          ·
            refine ⟨3209050050716002555910465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139366700477335037273643 3209050050716002555910465)
            ·
              refine ⟨2406787538037001916932849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3209050050716002555910465 2406787538037001916932849)
              ·
                refine ⟨1805090653527751437699637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406787538037001916932849 1805090653527751437699637)
                ·
                  refine ⟨169227248768226697284341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805090653527751437699637 169227248768226697284341)
                  ·
                    rfl

theorem cell23_2966120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 5].length) (baseStart_2966120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966120 prefixEnd_2966120 := by exact prefixLift 2966120
  have htrace : WordTrace (prefixWord ++ tailWord_2966120) baseStart_2966120 baseEnd_2966120 := by
    simpa [prefixWord, tailWord_2966120, baseEnd_2966120] using wordTrace_append hprefix tailTrace_2966120
  have hstable : (prefixWord ++ tailWord_2966120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966120).length < 2 ^ (prefixWord ++ tailWord_2966120).sum := by decide
  have hdescent : baseEnd_2966120 < baseStart_2966120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966122 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2966122 : Nat := 118140960795 + 2966122 * 2 ^ 59
def prefixEnd_2966122 : Nat := 4983230072969 + 3 ^ 40 * 2966122 * 2
def baseEnd_2966122 : Nat := 1523046265875349267734059

theorem tailTrace_2966122 : CollatzResearch.WordTrace tailWord_2966122 prefixEnd_2966122 1523046265875349267734059 := by
  unfold tailWord_2966122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27045839240063510538087155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72122237973502694768232413 27045839240063510538087155)
  ·
    refine ⟨40568758860095265807130733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27045839240063510538087155 40568758860095265807130733)
    ·
      refine ⟨15213284572535724677674025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40568758860095265807130733 15213284572535724677674025)
      ·
        refine ⟨11409963429401793508255519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15213284572535724677674025 11409963429401793508255519)
        ·
          refine ⟨17114945144102690262383279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11409963429401793508255519 17114945144102690262383279)
          ·
            refine ⟨25672417716154035393574919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17114945144102690262383279 25672417716154035393574919)
            ·
              refine ⟨38508626574231053090362379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25672417716154035393574919 38508626574231053090362379)
              ·
                refine ⟨57762939861346579635543569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38508626574231053090362379 57762939861346579635543569)
                ·
                  refine ⟨43322204896009934726657677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57762939861346579635543569 43322204896009934726657677)
                  ·
                    refine ⟨16245826836003725522496629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43322204896009934726657677 16245826836003725522496629)
                    ·
                      refine ⟨1523046265875349267734059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16245826836003725522496629 1523046265875349267734059)
                      ·
                        rfl

theorem cell23_2966122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2966122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966122 prefixEnd_2966122 := by exact prefixLift 2966122
  have htrace : WordTrace (prefixWord ++ tailWord_2966122) baseStart_2966122 baseEnd_2966122 := by
    simpa [prefixWord, tailWord_2966122, baseEnd_2966122] using wordTrace_append hprefix tailTrace_2966122
  have hstable : (prefixWord ++ tailWord_2966122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966122).length < 2 ^ (prefixWord ++ tailWord_2966122).sum := by decide
  have hdescent : baseEnd_2966122 < baseStart_2966122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966169 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 3]
def baseStart_2966169 : Nat := 118140960795 + 2966169 * 2 ^ 59
def prefixEnd_2966169 : Nat := 4983230072969 + 3 ^ 40 * 2966169 * 2
def baseEnd_2966169 : Nat := 1523070399466110583846343

theorem tailTrace_2966169 : CollatzResearch.WordTrace tailWord_2966169 prefixEnd_2966169 1523070399466110583846343 := by
  unfold tailWord_2966169
  simp only [CollatzResearch.WordTrace]
  refine ⟨108185071191083769179309561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72123380794055846119539707 108185071191083769179309561)
  ·
    refine ⟨81138803393312826884482171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108185071191083769179309561 81138803393312826884482171)
    ·
      refine ⟨121708205089969240326723257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81138803393312826884482171 121708205089969240326723257)
      ·
        refine ⟨91281153817476930245042443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121708205089969240326723257 91281153817476930245042443)
        ·
          refine ⟨136921730726215395367563665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91281153817476930245042443 136921730726215395367563665)
          ·
            refine ⟨102691298044661546525672749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136921730726215395367563665 102691298044661546525672749)
            ·
              refine ⟨38509236766748079947127281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102691298044661546525672749 38509236766748079947127281)
              ·
                refine ⟨28881927575061059960345461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38509236766748079947127281 28881927575061059960345461)
                ·
                  refine ⟨2707680710161974371282387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28881927575061059960345461 2707680710161974371282387)
                  ·
                    refine ⟨4061521065242961556923581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707680710161974371282387 4061521065242961556923581)
                    ·
                      refine ⟨1523070399466110583846343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061521065242961556923581 1523070399466110583846343)
                      ·
                        rfl

theorem cell23_2966169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_2966169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966169 prefixEnd_2966169 := by exact prefixLift 2966169
  have htrace : WordTrace (prefixWord ++ tailWord_2966169) baseStart_2966169 baseEnd_2966169 := by
    simpa [prefixWord, tailWord_2966169, baseEnd_2966169] using wordTrace_append hprefix tailTrace_2966169
  have hstable : (prefixWord ++ tailWord_2966169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966169).length < 2 ^ (prefixWord ++ tailWord_2966169).sum := by decide
  have hdescent : baseEnd_2966169 < baseStart_2966169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966176 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 6]
def baseStart_2966176 : Nat := 118140960795 + 2966176 * 2 ^ 59
def prefixEnd_2966176 : Nat := 4983230072969 + 3 ^ 40 * 2966176 * 2
def baseEnd_2966176 : Nat := 169230443758965784050979

theorem tailTrace_2966176 : CollatzResearch.WordTrace tailWord_2966176 prefixEnd_2966176 169230443758965784050979 := by
  unfold tailWord_2966176
  simp only [CollatzResearch.WordTrace]
  refine ⟨54092663251029204687407191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72123551001372272916542921 54092663251029204687407191)
  ·
    refine ⟨81138994876543807031110787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54092663251029204687407191 81138994876543807031110787)
    ·
      refine ⟨121708492314815710546666181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81138994876543807031110787 121708492314815710546666181)
      ·
        refine ⟨22820342309027945727499909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121708492314815710546666181 22820342309027945727499909)
        ·
          refine ⟨4278814182942739823906233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22820342309027945727499909 4278814182942739823906233)
          ·
            refine ⟨3209110637207054867929675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278814182942739823906233 3209110637207054867929675)
            ·
              refine ⟨4813665955810582301894513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209110637207054867929675 4813665955810582301894513)
              ·
                refine ⟨3610249466857936726420885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813665955810582301894513 3610249466857936726420885)
                ·
                  refine ⟨169230443758965784050979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3610249466857936726420885 169230443758965784050979)
                  ·
                    rfl

theorem cell23_2966176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_2966176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966176 prefixEnd_2966176 := by exact prefixLift 2966176
  have htrace : WordTrace (prefixWord ++ tailWord_2966176) baseStart_2966176 baseEnd_2966176 := by
    simpa [prefixWord, tailWord_2966176, baseEnd_2966176] using wordTrace_append hprefix tailTrace_2966176
  have hstable : (prefixWord ++ tailWord_2966176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966176).length < 2 ^ (prefixWord ++ tailWord_2966176).sum := by decide
  have hdescent : baseEnd_2966176 < baseStart_2966176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966193 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 6]
def baseStart_2966193 : Nat := 118140960795 + 2966193 * 2 ^ 59
def prefixEnd_2966193 : Nat := 4983230072969 + 3 ^ 40 * 2966193 * 2
def baseEnd_2966193 : Nat := 169231413666868721105137

theorem tailTrace_2966193 : CollatzResearch.WordTrace tailWord_2966193 prefixEnd_2966193 169231413666868721105137 := by
  unfold tailWord_2966193
  simp only [CollatzResearch.WordTrace]
  refine ⟨108185946542996821278183233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72123964361997880852122155 108185946542996821278183233)
  ·
    refine ⟨81139459907247615958637425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108185946542996821278183233 81139459907247615958637425)
    ·
      refine ⟨60854594930435711968978069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81139459907247615958637425 60854594930435711968978069)
      ·
        refine ⟨2852559137364173998545847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60854594930435711968978069 2852559137364173998545847)
        ·
          refine ⟨4278838706046260997818771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852559137364173998545847 4278838706046260997818771)
          ·
            refine ⟨6418258059069391496728157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278838706046260997818771 6418258059069391496728157)
            ·
              refine ⟨2406846772151021811273059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6418258059069391496728157 2406846772151021811273059)
              ·
                refine ⟨3610270158226532716909589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406846772151021811273059 3610270158226532716909589)
                ·
                  refine ⟨169231413666868721105137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3610270158226532716909589 169231413666868721105137)
                  ·
                    rfl

theorem cell23_2966193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 6].length) (baseStart_2966193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966193 prefixEnd_2966193 := by exact prefixLift 2966193
  have htrace : WordTrace (prefixWord ++ tailWord_2966193) baseStart_2966193 baseEnd_2966193 := by
    simpa [prefixWord, tailWord_2966193, baseEnd_2966193] using wordTrace_append hprefix tailTrace_2966193
  have hstable : (prefixWord ++ tailWord_2966193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966193).length < 2 ^ (prefixWord ++ tailWord_2966193).sum := by decide
  have hdescent : baseEnd_2966193 < baseStart_2966193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966206 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2966206 : Nat := 118140960795 + 2966206 * 2 ^ 59
def prefixEnd_2966206 : Nat := 4983230072969 + 3 ^ 40 * 2966206 * 2
def baseEnd_2966206 : Nat := 507696466083442313027891

theorem tailTrace_2966206 : CollatzResearch.WordTrace tailWord_2966206 prefixEnd_2966206 507696466083442313027891 := by
  unfold tailWord_2966206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13523302586493715562300809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72124280461299816332270981 13523302586493715562300809)
  ·
    refine ⟨10142476939870286671725607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13523302586493715562300809 10142476939870286671725607)
    ·
      refine ⟨15213715409805430007588411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142476939870286671725607 15213715409805430007588411)
      ·
        refine ⟨22820573114708145011382617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15213715409805430007588411 22820573114708145011382617)
        ·
          refine ⟨17115429836031108758536963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22820573114708145011382617 17115429836031108758536963)
          ·
            refine ⟨25673144754046663137805445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17115429836031108758536963 25673144754046663137805445)
            ·
              refine ⟨4813714641383749338338521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25673144754046663137805445 4813714641383749338338521)
              ·
                refine ⟨3610285981037812003753891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813714641383749338338521 3610285981037812003753891)
                ·
                  refine ⟨5415428971556718005630837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610285981037812003753891 5415428971556718005630837)
                  ·
                    refine ⟨507696466083442313027891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5415428971556718005630837 507696466083442313027891)
                    ·
                      rfl

theorem cell23_2966206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2966206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966206 prefixEnd_2966206 := by exact prefixLift 2966206
  have htrace : WordTrace (prefixWord ++ tailWord_2966206) baseStart_2966206 baseEnd_2966206 := by
    simpa [prefixWord, tailWord_2966206, baseEnd_2966206] using wordTrace_append hprefix tailTrace_2966206
  have hstable : (prefixWord ++ tailWord_2966206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966206).length < 2 ^ (prefixWord ++ tailWord_2966206).sum := by decide
  have hdescent : baseEnd_2966206 < baseStart_2966206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966214 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2966214 : Nat := 118140960795 + 2966214 * 2 ^ 59
def prefixEnd_2966214 : Nat := 4983230072969 + 3 ^ 40 * 2966214 * 2
def baseEnd_2966214 : Nat := 507697835365187635927879

theorem tailTrace_2966214 : CollatzResearch.WordTrace tailWord_2966214 prefixEnd_2966214 507697835365187635927879 := by
  unfold tailWord_2966214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380834764872523183271803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72124474983947161243131797 3380834764872523183271803)
  ·
    refine ⟨5071252147308784774907705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380834764872523183271803 5071252147308784774907705)
    ·
      refine ⟨3803439110481588581180779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5071252147308784774907705 3803439110481588581180779)
      ·
        refine ⟨5705158665722382871771169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803439110481588581180779 5705158665722382871771169)
        ·
          refine ⟨4278868999291787153828377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5705158665722382871771169 4278868999291787153828377)
          ·
            refine ⟨3209151749468840365371283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278868999291787153828377 3209151749468840365371283)
            ·
              refine ⟨4813727624203260548056925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209151749468840365371283 4813727624203260548056925)
              ·
                refine ⟨1805147859076222705521347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4813727624203260548056925 1805147859076222705521347)
                ·
                  refine ⟨2707721788614334058282021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805147859076222705521347 2707721788614334058282021)
                  ·
                    refine ⟨507697835365187635927879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707721788614334058282021 507697835365187635927879)
                    ·
                      rfl

theorem cell23_2966214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2966214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966214 prefixEnd_2966214 := by exact prefixLift 2966214
  have htrace : WordTrace (prefixWord ++ tailWord_2966214) baseStart_2966214 baseEnd_2966214 := by
    simpa [prefixWord, tailWord_2966214, baseEnd_2966214] using wordTrace_append hprefix tailTrace_2966214
  have hstable : (prefixWord ++ tailWord_2966214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966214).length < 2 ^ (prefixWord ++ tailWord_2966214).sum := by decide
  have hdescent : baseEnd_2966214 < baseStart_2966214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966220 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2966220 : Nat := 118140960795 + 2966220 * 2 ^ 59
def prefixEnd_2966220 : Nat := 4983230072969 + 3 ^ 40 * 2966220 * 2
def baseEnd_2966220 : Nat := 1523096586979489884308609

theorem tailTrace_2966220 : CollatzResearch.WordTrace tailWord_2966220 prefixEnd_2966220 1523096586979489884308609 := by
  unfold tailWord_2966220
  simp only [CollatzResearch.WordTrace]
  refine ⟨54093465656949502444708057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72124620875932669926277409 54093465656949502444708057)
  ·
    refine ⟨40570099242712126833531043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54093465656949502444708057 40570099242712126833531043)
    ·
      refine ⟨60855148864068190250296565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40570099242712126833531043 60855148864068190250296565)
      ·
        refine ⟨5705170206006392835965303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60855148864068190250296565 5705170206006392835965303)
        ·
          refine ⟨8557755309009589253947955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705170206006392835965303 8557755309009589253947955)
          ·
            refine ⟨12836632963514383880921933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8557755309009589253947955 12836632963514383880921933)
            ·
              refine ⟨4813737361317893955345725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12836632963514383880921933 4813737361317893955345725)
              ·
                refine ⟨1805151510494210233254647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4813737361317893955345725 1805151510494210233254647)
                ·
                  refine ⟨2707727265741315349881971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805151510494210233254647 2707727265741315349881971)
                  ·
                    refine ⟨4061590898611973024822957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707727265741315349881971 4061590898611973024822957)
                    ·
                      refine ⟨1523096586979489884308609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061590898611973024822957 1523096586979489884308609)
                      ·
                        rfl

theorem cell23_2966220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2966220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966220 prefixEnd_2966220 := by exact prefixLift 2966220
  have htrace : WordTrace (prefixWord ++ tailWord_2966220) baseStart_2966220 baseEnd_2966220 := by
    simpa [prefixWord, tailWord_2966220, baseEnd_2966220] using wordTrace_append hprefix tailTrace_2966220
  have hstable : (prefixWord ++ tailWord_2966220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966220).length < 2 ^ (prefixWord ++ tailWord_2966220).sum := by decide
  have hdescent : baseEnd_2966220 < baseStart_2966220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966232 : List Nat := [2, 1, 2, 2, 3, 2, 11]
def baseStart_2966232 : Nat := 118140960795 + 2966232 * 2 ^ 59
def prefixEnd_2966232 : Nat := 4983230072969 + 3 ^ 40 * 2966232 * 2
def baseEnd_2966232 : Nat := 18803737638856096757513

theorem tailTrace_2966232 : CollatzResearch.WordTrace tailWord_2966232 prefixEnd_2966232 18803737638856096757513 := by
  unfold tailWord_2966232
  simp only [CollatzResearch.WordTrace]
  refine ⟨54093684494927765469426475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72124912659903687292568633 54093684494927765469426475)
  ·
    refine ⟨81140526742391648204139713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54093684494927765469426475 81140526742391648204139713)
    ·
      refine ⟨60855395056793736153104785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81140526742391648204139713 60855395056793736153104785)
      ·
        refine ⟨45641546292595302114828589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60855395056793736153104785 45641546292595302114828589)
        ·
          refine ⟨17115579859723238293060721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45641546292595302114828589 17115579859723238293060721)
          ·
            refine ⟨12836684894792428719795541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17115579859723238293060721 12836684894792428719795541)
            ·
              refine ⟨18803737638856096757513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12836684894792428719795541 18803737638856096757513)
              ·
                rfl

theorem cell23_2966232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 11].length) (baseStart_2966232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966232 prefixEnd_2966232 := by exact prefixLift 2966232
  have htrace : WordTrace (prefixWord ++ tailWord_2966232) baseStart_2966232 baseEnd_2966232 := by
    simpa [prefixWord, tailWord_2966232, baseEnd_2966232] using wordTrace_append hprefix tailTrace_2966232
  have hstable : (prefixWord ++ tailWord_2966232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966232).length < 2 ^ (prefixWord ++ tailWord_2966232).sum := by decide
  have hdescent : baseEnd_2966232 < baseStart_2966232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966252 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2966252 : Nat := 118140960795 + 2966252 * 2 ^ 59
def prefixEnd_2966252 : Nat := 4983230072969 + 3 ^ 40 * 2966252 * 2
def baseEnd_2966252 : Nat := 1523113018360433759108461

theorem tailTrace_2966252 : CollatzResearch.WordTrace tailWord_2966252 prefixEnd_2966252 1523113018360433759108461 := by
  unfold tailWord_2966252
  simp only [CollatzResearch.WordTrace]
  refine ⟨54094049224891537177290505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72125398966522049569720673 54094049224891537177290505)
  ·
    refine ⟨40570536918668652882967879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54094049224891537177290505 40570536918668652882967879)
    ·
      refine ⟨60855805378002979324451819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40570536918668652882967879 60855805378002979324451819)
      ·
        refine ⟨91283708067004468986677729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60855805378002979324451819 91283708067004468986677729)
        ·
          refine ⟨68462781050253351740008297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91283708067004468986677729 68462781050253351740008297)
          ·
            refine ⟨51347085787690013805006223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68462781050253351740008297 51347085787690013805006223)
            ·
              refine ⟨77020628681535020707509335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51347085787690013805006223 77020628681535020707509335)
              ·
                refine ⟨115530943022302531061264003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77020628681535020707509335 115530943022302531061264003)
                ·
                  refine ⟨173296414533453796591896005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115530943022302531061264003 173296414533453796591896005)
                  ·
                    refine ⟨32493077725022586860980501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173296414533453796591896005 32493077725022586860980501)
                    ·
                      refine ⟨1523113018360433759108461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32493077725022586860980501 1523113018360433759108461)
                      ·
                        rfl

theorem cell23_2966252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2966252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966252 prefixEnd_2966252 := by exact prefixLift 2966252
  have htrace : WordTrace (prefixWord ++ tailWord_2966252) baseStart_2966252 baseEnd_2966252 := by
    simpa [prefixWord, tailWord_2966252, baseEnd_2966252] using wordTrace_append hprefix tailTrace_2966252
  have hstable : (prefixWord ++ tailWord_2966252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966252).length < 2 ^ (prefixWord ++ tailWord_2966252).sum := by decide
  have hdescent : baseEnd_2966252 < baseStart_2966252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966259 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 3]
def baseStart_2966259 : Nat := 118140960795 + 2966259 * 2 ^ 59
def prefixEnd_2966259 : Nat := 4983230072969 + 3 ^ 40 * 2966259 * 2
def baseEnd_2966259 : Nat := 1523116612725015231720929

theorem tailTrace_2966259 : CollatzResearch.WordTrace tailWord_2966259 prefixEnd_2966259 1523116612725015231720929 := by
  unfold tailWord_2966259
  simp only [CollatzResearch.WordTrace]
  refine ⟨108188353760757714550085831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72125569173838476366723887 108188353760757714550085831)
  ·
    refine ⟨162282530641136571825128747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108188353760757714550085831 162282530641136571825128747)
    ·
      refine ⟨243423795961704857737693121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162282530641136571825128747 243423795961704857737693121)
      ·
        refine ⟨182567846971278643303269841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243423795961704857737693121 182567846971278643303269841)
        ·
          refine ⟨136925885228458982477452381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182567846971278643303269841 136925885228458982477452381)
          ·
            refine ⟨51347206960672118429044643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136925885228458982477452381 51347206960672118429044643)
            ·
              refine ⟨77020810441008177643566965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51347206960672118429044643 77020810441008177643566965)
              ·
                refine ⟨7220700978844516654084403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77020810441008177643566965 7220700978844516654084403)
                ·
                  refine ⟨10831051468266774981126605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220700978844516654084403 10831051468266774981126605)
                  ·
                    refine ⟨4061644300600040617922477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10831051468266774981126605 4061644300600040617922477)
                    ·
                      refine ⟨1523116612725015231720929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061644300600040617922477 1523116612725015231720929)
                      ·
                        rfl

theorem cell23_2966259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_2966259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966259 prefixEnd_2966259 := by exact prefixLift 2966259
  have htrace : WordTrace (prefixWord ++ tailWord_2966259) baseStart_2966259 baseEnd_2966259 := by
    simpa [prefixWord, tailWord_2966259, baseEnd_2966259] using wordTrace_append hprefix tailTrace_2966259
  have hstable : (prefixWord ++ tailWord_2966259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966259).length < 2 ^ (prefixWord ++ tailWord_2966259).sum := by decide
  have hdescent : baseEnd_2966259 < baseStart_2966259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966260 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2966260 : Nat := 118140960795 + 2966260 * 2 ^ 59
def prefixEnd_2966260 : Nat := 4983230072969 + 3 ^ 40 * 2966260 * 2
def baseEnd_2966260 : Nat := 1523117126205669727808425

theorem tailTrace_2966260 : CollatzResearch.WordTrace tailWord_2966260 prefixEnd_2966260 1523117126205669727808425 := by
  unfold tailWord_2966260
  simp only [CollatzResearch.WordTrace]
  refine ⟨54094195116877045860436117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72125593489169394480581489 54094195116877045860436117)
  ·
    refine ⟨2535665396103611524707943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54094195116877045860436117 2535665396103611524707943)
    ·
      refine ⟨3803498094155417287061915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535665396103611524707943 3803498094155417287061915)
      ·
        refine ⟨5705247141233125930592873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803498094155417287061915 5705247141233125930592873)
        ·
          refine ⟨4278935355924844447944655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5705247141233125930592873 4278935355924844447944655)
          ·
            refine ⟨6418403033887266671916983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278935355924844447944655 6418403033887266671916983)
            ·
              refine ⟨9627604550830900007875475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418403033887266671916983 9627604550830900007875475)
              ·
                refine ⟨14441406826246350011813213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9627604550830900007875475 14441406826246350011813213)
                ·
                  refine ⟨5415527559842381254429955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14441406826246350011813213 5415527559842381254429955)
                  ·
                    refine ⟨8123291339763571881644933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5415527559842381254429955 8123291339763571881644933)
                    ·
                      refine ⟨1523117126205669727808425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8123291339763571881644933 1523117126205669727808425)
                      ·
                        rfl

theorem cell23_2966260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2966260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966260 prefixEnd_2966260 := by exact prefixLift 2966260
  have htrace : WordTrace (prefixWord ++ tailWord_2966260) baseStart_2966260 baseEnd_2966260 := by
    simpa [prefixWord, tailWord_2966260, baseEnd_2966260] using wordTrace_append hprefix tailTrace_2966260
  have hstable : (prefixWord ++ tailWord_2966260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966260).length < 2 ^ (prefixWord ++ tailWord_2966260).sum := by decide
  have hdescent : baseEnd_2966260 < baseStart_2966260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966276 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2966276 : Nat := 118140960795 + 2966276 * 2 ^ 59
def prefixEnd_2966276 : Nat := 4983230072969 + 3 ^ 40 * 2966276 * 2
def baseEnd_2966276 : Nat := 1523125341896141665208351

theorem tailTrace_2966276 : CollatzResearch.WordTrace tailWord_2966276 prefixEnd_2966276 1523125341896141665208351 := by
  unfold tailWord_2966276
  simp only [CollatzResearch.WordTrace]
  refine ⟨54094486900848063226727341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72125982534464084302303121 54094486900848063226727341)
  ·
    refine ⟨20285432587818023710022753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54094486900848063226727341 20285432587818023710022753)
    ·
      refine ⟨15214074440863517782517065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20285432587818023710022753 15214074440863517782517065)
      ·
        refine ⟨11410555830647638336887799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15214074440863517782517065 11410555830647638336887799)
        ·
          refine ⟨17115833745971457505331699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410555830647638336887799 17115833745971457505331699)
          ·
            refine ⟨25673750618957186257997549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17115833745971457505331699 25673750618957186257997549)
            ·
              refine ⟨9627656482108944846749081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25673750618957186257997549 9627656482108944846749081)
              ·
                refine ⟨7220742361581708635061811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9627656482108944846749081 7220742361581708635061811)
                ·
                  refine ⟨10831113542372562952592717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220742361581708635061811 10831113542372562952592717)
                  ·
                    refine ⟨4061667578389711107222269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10831113542372562952592717 4061667578389711107222269)
                    ·
                      refine ⟨1523125341896141665208351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061667578389711107222269 1523125341896141665208351)
                      ·
                        rfl

theorem cell23_2966276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2966276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966276 prefixEnd_2966276 := by exact prefixLift 2966276
  have htrace : WordTrace (prefixWord ++ tailWord_2966276) baseStart_2966276 baseEnd_2966276 := by
    simpa [prefixWord, tailWord_2966276, baseEnd_2966276] using wordTrace_append hprefix tailTrace_2966276
  have hstable : (prefixWord ++ tailWord_2966276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966276).length < 2 ^ (prefixWord ++ tailWord_2966276).sum := by decide
  have hdescent : baseEnd_2966276 < baseStart_2966276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966293 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_2966293 : Nat := 118140960795 + 2966293 * 2 ^ 59
def prefixEnd_2966293 : Nat := 4983230072969 + 3 ^ 40 * 2966293 * 2
def baseEnd_2966293 : Nat := 1523134071067268098695773

theorem tailTrace_2966293 : CollatzResearch.WordTrace tailWord_2966293 prefixEnd_2966293 1523134071067268098695773 := by
  unfold tailWord_2966293
  simp only [CollatzResearch.WordTrace]
  refine ⟨108189593842634538356823533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72126395895089692237882355 108189593842634538356823533)
  ·
    refine ⟨40571097690987951883808825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108189593842634538356823533 40571097690987951883808825)
    ·
      refine ⟨30428323268240963912856619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40571097690987951883808825 30428323268240963912856619)
      ·
        refine ⟨45642484902361445869284929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30428323268240963912856619 45642484902361445869284929)
        ·
          refine ⟨34231863676771084401963697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45642484902361445869284929 34231863676771084401963697)
          ·
            refine ⟨25673897757578313301472773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34231863676771084401963697 25673897757578313301472773)
            ·
              refine ⟨4813855829545933744026145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25673897757578313301472773 4813855829545933744026145)
              ·
                refine ⟨3610391872159450308019609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813855829545933744026145 3610391872159450308019609)
                ·
                  refine ⟨2707793904119587731014707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610391872159450308019609 2707793904119587731014707)
                  ·
                    refine ⟨4061690856179381596522061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707793904119587731014707 4061690856179381596522061)
                    ·
                      refine ⟨1523134071067268098695773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061690856179381596522061 1523134071067268098695773)
                      ·
                        rfl

theorem cell23_2966293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_2966293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966293 prefixEnd_2966293 := by exact prefixLift 2966293
  have htrace : WordTrace (prefixWord ++ tailWord_2966293) baseStart_2966293 baseEnd_2966293 := by
    simpa [prefixWord, tailWord_2966293, baseEnd_2966293] using wordTrace_append hprefix tailTrace_2966293
  have hstable : (prefixWord ++ tailWord_2966293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966293).length < 2 ^ (prefixWord ++ tailWord_2966293).sum := by decide
  have hdescent : baseEnd_2966293 < baseStart_2966293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966309 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_2966309 : Nat := 118140960795 + 2966309 * 2 ^ 59
def prefixEnd_2966309 : Nat := 4983230072969 + 3 ^ 40 * 2966309 * 2
def baseEnd_2966309 : Nat := 507714095585913345365233

theorem tailTrace_2966309 : CollatzResearch.WordTrace tailWord_2966309 prefixEnd_2966309 507714095585913345365233 := by
  unfold tailWord_2966309
  simp only [CollatzResearch.WordTrace]
  refine ⟨108190177410576573089405981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72126784940384382059603987 108190177410576573089405981)
  ·
    refine ⟨40571316528966214908527243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108190177410576573089405981 40571316528966214908527243)
    ·
      refine ⟨60856974793449322362790865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40571316528966214908527243 60856974793449322362790865)
      ·
        refine ⟨45642731095086991772093149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60856974793449322362790865 45642731095086991772093149)
        ·
          refine ⟨17116024160657621914534931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45642731095086991772093149 17116024160657621914534931)
          ·
            refine ⟨25674036240986432871802397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17116024160657621914534931 25674036240986432871802397)
            ·
              refine ⟨9627763590369912326925899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25674036240986432871802397 9627763590369912326925899)
              ·
                refine ⟨14441645385554868490388849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9627763590369912326925899 14441645385554868490388849)
                ·
                  refine ⟨10831234039166151367791637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14441645385554868490388849 10831234039166151367791637)
                  ·
                    refine ⟨507714095585913345365233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10831234039166151367791637 507714095585913345365233)
                    ·
                      rfl

theorem cell23_2966309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_2966309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966309 prefixEnd_2966309 := by exact prefixLift 2966309
  have htrace : WordTrace (prefixWord ++ tailWord_2966309) baseStart_2966309 baseEnd_2966309 := by
    simpa [prefixWord, tailWord_2966309, baseEnd_2966309] using wordTrace_append hprefix tailTrace_2966309
  have hstable : (prefixWord ++ tailWord_2966309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966309).length < 2 ^ (prefixWord ++ tailWord_2966309).sum := by decide
  have hdescent : baseEnd_2966309 < baseStart_2966309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966337 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2966337 : Nat := 118140960795 + 2966337 * 2 ^ 59
def prefixEnd_2966337 : Nat := 4983230072969 + 3 ^ 40 * 2966337 * 2
def baseEnd_2966337 : Nat := 1523156664216065926545571

theorem tailTrace_2966337 : CollatzResearch.WordTrace tailWord_2966337 prefixEnd_2966337 1523156664216065926545571 := by
  unfold tailWord_2966337
  simp only [CollatzResearch.WordTrace]
  refine ⟨108191198654475133871425265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72127465769650089247616843 108191198654475133871425265)
  ·
    refine ⟨81143398990856350403568949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108191198654475133871425265 81143398990856350403568949)
    ·
      refine ⟨7607193655392782850334589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81143398990856350403568949 7607193655392782850334589)
      ·
        refine ⟨2852697620772293568875471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7607193655392782850334589 2852697620772293568875471)
        ·
          refine ⟨4279046431158440353313207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852697620772293568875471 4279046431158440353313207)
          ·
            refine ⟨6418569646737660529969811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279046431158440353313207 6418569646737660529969811)
            ·
              refine ⟨9627854470106490794954717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418569646737660529969811 9627854470106490794954717)
              ·
                refine ⟨3610445426289934048108019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9627854470106490794954717 3610445426289934048108019)
                ·
                  refine ⟨5415668139434901072162029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610445426289934048108019 5415668139434901072162029)
                  ·
                    refine ⟨2030875552288087902060761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5415668139434901072162029 2030875552288087902060761)
                    ·
                      refine ⟨1523156664216065926545571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2030875552288087902060761 1523156664216065926545571)
                      ·
                        rfl

theorem cell23_2966337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2966337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966337 prefixEnd_2966337 := by exact prefixLift 2966337
  have htrace : WordTrace (prefixWord ++ tailWord_2966337) baseStart_2966337 baseEnd_2966337 := by
    simpa [prefixWord, tailWord_2966337, baseEnd_2966337] using wordTrace_append hprefix tailTrace_2966337
  have hstable : (prefixWord ++ tailWord_2966337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966337).length < 2 ^ (prefixWord ++ tailWord_2966337).sum := by decide
  have hdescent : baseEnd_2966337 < baseStart_2966337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966369 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2966369 : Nat := 118140960795 + 2966369 * 2 ^ 59
def prefixEnd_2966369 : Nat := 4983230072969 + 3 ^ 40 * 2966369 * 2
def baseEnd_2966369 : Nat := 507724365199003267115141

theorem tailTrace_2966369 : CollatzResearch.WordTrace tailWord_2966369 prefixEnd_2966369 507724365199003267115141 := by
  unfold tailWord_2966369
  simp only [CollatzResearch.WordTrace]
  refine ⟨108192365790359203336590161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72128243860239468891060107 108192365790359203336590161)
  ·
    refine ⟨81144274342769402502442621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108192365790359203336590161 81144274342769402502442621)
    ·
      refine ⟨30429102878538525938415983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81144274342769402502442621 30429102878538525938415983)
      ·
        refine ⟨45643654317807788907623975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30429102878538525938415983 45643654317807788907623975)
        ·
          refine ⟨68465481476711683361435963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45643654317807788907623975 68465481476711683361435963)
          ·
            refine ⟨102698222215067525042153945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68465481476711683361435963 102698222215067525042153945)
            ·
              refine ⟨77023666661300643781615459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102698222215067525042153945 77023666661300643781615459)
              ·
                refine ⟨115535499991950965672423189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77023666661300643781615459 115535499991950965672423189)
                ·
                  refine ⟨5415726562122701515894837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115535499991950965672423189 5415726562122701515894837)
                  ·
                    refine ⟨507724365199003267115141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5415726562122701515894837 507724365199003267115141)
                    ·
                      rfl

theorem cell23_2966369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2966369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966369 prefixEnd_2966369 := by exact prefixLift 2966369
  have htrace : WordTrace (prefixWord ++ tailWord_2966369) baseStart_2966369 baseEnd_2966369 := by
    simpa [prefixWord, tailWord_2966369, baseEnd_2966369] using wordTrace_append hprefix tailTrace_2966369
  have hstable : (prefixWord ++ tailWord_2966369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966369).length < 2 ^ (prefixWord ++ tailWord_2966369).sum := by decide
  have hdescent : baseEnd_2966369 < baseStart_2966369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966390 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2966390 : Nat := 118140960795 + 2966390 * 2 ^ 59
def prefixEnd_2966390 : Nat := 4983230072969 + 3 ^ 40 * 2966390 * 2
def baseEnd_2966390 : Nat := 169242653187861579909203

theorem tailTrace_2966390 : CollatzResearch.WordTrace tailWord_2966390 prefixEnd_2966390 169242653187861579909203 := by
  unfold tailWord_2966390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762070732705195245194039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72128754482188749282069749 6762070732705195245194039)
  ·
    refine ⟨10143106099057792867791059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6762070732705195245194039 10143106099057792867791059)
    ·
      refine ⟨15214659148586689301686589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10143106099057792867791059 15214659148586689301686589)
      ·
        refine ⟨5705497180720008488132471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15214659148586689301686589 5705497180720008488132471)
        ·
          refine ⟨8558245771080012732198707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705497180720008488132471 8558245771080012732198707)
          ·
            refine ⟨12837368656620019098298061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8558245771080012732198707 12837368656620019098298061)
            ·
              refine ⟨4814013246232507161861773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12837368656620019098298061 4814013246232507161861773)
              ·
                refine ⟨1805254967337190185698165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4814013246232507161861773 1805254967337190185698165)
                ·
                  refine ⟨169242653187861579909203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805254967337190185698165 169242653187861579909203)
                  ·
                    rfl

theorem cell23_2966390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2966390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966390 prefixEnd_2966390 := by exact prefixLift 2966390
  have htrace : WordTrace (prefixWord ++ tailWord_2966390) baseStart_2966390 baseEnd_2966390 := by
    simpa [prefixWord, tailWord_2966390, baseEnd_2966390] using wordTrace_append hprefix tailTrace_2966390
  have hstable : (prefixWord ++ tailWord_2966390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966390).length < 2 ^ (prefixWord ++ tailWord_2966390).sum := by decide
  have hdescent : baseEnd_2966390 < baseStart_2966390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966419 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4]
def baseStart_2966419 : Nat := 118140960795 + 2966419 * 2 ^ 59
def prefixEnd_2966419 : Nat := 4983230072969 + 3 ^ 40 * 2966419 * 2
def baseEnd_2966419 : Nat := 1523198769629734605720193

theorem tailTrace_2966419 : CollatzResearch.WordTrace tailWord_2966419 prefixEnd_2966419 1523198769629734605720193 := by
  unfold tailWord_2966419
  simp only [CollatzResearch.WordTrace]
  refine ⟨108194189440178061875910311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72129459626785374583940207 108194189440178061875910311)
  ·
    refine ⟨162291284160267092813865467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108194189440178061875910311 162291284160267092813865467)
    ·
      refine ⟨243436926240400639220798201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162291284160267092813865467 243436926240400639220798201)
      ·
        refine ⟨182577694680300479415598651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243436926240400639220798201 182577694680300479415598651)
        ·
          refine ⟨273866542020450719123397977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182577694680300479415598651 273866542020450719123397977)
          ·
            refine ⟨205399906515338039342548483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273866542020450719123397977 205399906515338039342548483)
            ·
              refine ⟨308099859773007059013822725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205399906515338039342548483 308099859773007059013822725)
              ·
                refine ⟨57768723707438823565091761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308099859773007059013822725 57768723707438823565091761)
                ·
                  refine ⟨43326542780579117673818821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57768723707438823565091761 43326542780579117673818821)
                  ·
                    refine ⟨8123726771358584563841029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43326542780579117673818821 8123726771358584563841029)
                    ·
                      refine ⟨1523198769629734605720193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8123726771358584563841029 1523198769629734605720193)
                      ·
                        rfl

theorem cell23_2966419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_2966419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966419 prefixEnd_2966419 := by exact prefixLift 2966419
  have htrace : WordTrace (prefixWord ++ tailWord_2966419) baseStart_2966419 baseEnd_2966419 := by
    simpa [prefixWord, tailWord_2966419, baseEnd_2966419] using wordTrace_append hprefix tailTrace_2966419
  have hstable : (prefixWord ++ tailWord_2966419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966419).length < 2 ^ (prefixWord ++ tailWord_2966419).sum := by decide
  have hdescent : baseEnd_2966419 < baseStart_2966419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966476 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_2966476 : Nat := 118140960795 + 2966476 * 2 ^ 59
def prefixEnd_2966476 : Nat := 4983230072969 + 3 ^ 40 * 2966476 * 2
def baseEnd_2966476 : Nat := 507742679342346960902477

theorem tailTrace_2966476 : CollatzResearch.WordTrace tailWord_2966476 prefixEnd_2966476 507742679342346960902477 := by
  unfold tailWord_2966476
  simp only [CollatzResearch.WordTrace]
  refine ⟨54098134200485780305367641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72130845600647707073823521 54098134200485780305367641)
  ·
    refine ⟨40573600650364335229025731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54098134200485780305367641 40573600650364335229025731)
    ·
      refine ⟨60860400975546502843538597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40573600650364335229025731 60860400975546502843538597)
      ·
        refine ⟨11411325182914969283163487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60860400975546502843538597 11411325182914969283163487)
        ·
          refine ⟨17116987774372453924745231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11411325182914969283163487 17116987774372453924745231)
          ·
            refine ⟨25675481661558680887117847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17116987774372453924745231 25675481661558680887117847)
            ·
              refine ⟨38513222492338021330676771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25675481661558680887117847 38513222492338021330676771)
              ·
                refine ⟨57769833738507031996015157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38513222492338021330676771 57769833738507031996015157)
                ·
                  refine ⟨5415921912985034249626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57769833738507031996015157 5415921912985034249626421)
                  ·
                    refine ⟨507742679342346960902477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5415921912985034249626421 507742679342346960902477)
                    ·
                      rfl

theorem cell23_2966476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_2966476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966476 prefixEnd_2966476 := by exact prefixLift 2966476
  have htrace : WordTrace (prefixWord ++ tailWord_2966476) baseStart_2966476 baseEnd_2966476 := by
    simpa [prefixWord, tailWord_2966476, baseEnd_2966476] using wordTrace_append hprefix tailTrace_2966476
  have hstable : (prefixWord ++ tailWord_2966476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966476).length < 2 ^ (prefixWord ++ tailWord_2966476).sum := by decide
  have hdescent : baseEnd_2966476 < baseStart_2966476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966490 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_2966490 : Nat := 118140960795 + 2966490 * 2 ^ 59
def prefixEnd_2966490 : Nat := 4983230072969 + 3 ^ 40 * 2966490 * 2
def baseEnd_2966490 : Nat := 1523235226756203827932367

theorem tailTrace_2966490 : CollatzResearch.WordTrace tailWord_2966490 prefixEnd_2966490 1523235226756203827932367 := by
  unfold tailWord_2966490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27049194755730210250436231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72131186015280560667829949 27049194755730210250436231)
  ·
    refine ⟨40573792133595315375654347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27049194755730210250436231 40573792133595315375654347)
    ·
      refine ⟨60860688200392973063481521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40573792133595315375654347 60860688200392973063481521)
      ·
        refine ⟨45645516150294729797611141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60860688200392973063481521 45645516150294729797611141)
        ·
          refine ⟨8558534278180261837052089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45645516150294729797611141 8558534278180261837052089)
          ·
            refine ⟨6418900708635196377789067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8558534278180261837052089 6418900708635196377789067)
            ·
              refine ⟨9628351062952794566683601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418900708635196377789067 9628351062952794566683601)
              ·
                refine ⟨7221263297214595925012701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9628351062952794566683601 7221263297214595925012701)
                ·
                  refine ⟨2707973736455473471879763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7221263297214595925012701 2707973736455473471879763)
                  ·
                    refine ⟨4061960604683210207819645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2707973736455473471879763 4061960604683210207819645)
                    ·
                      refine ⟨1523235226756203827932367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4061960604683210207819645 1523235226756203827932367)
                      ·
                        rfl

theorem cell23_2966490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_2966490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966490 prefixEnd_2966490 := by exact prefixLift 2966490
  have htrace : WordTrace (prefixWord ++ tailWord_2966490) baseStart_2966490 baseEnd_2966490 := by
    simpa [prefixWord, tailWord_2966490, baseEnd_2966490] using wordTrace_append hprefix tailTrace_2966490
  have hstable : (prefixWord ++ tailWord_2966490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966490).length < 2 ^ (prefixWord ++ tailWord_2966490).sum := by decide
  have hdescent : baseEnd_2966490 < baseStart_2966490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966493 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2966493 : Nat := 118140960795 + 2966493 * 2 ^ 59
def prefixEnd_2966493 : Nat := 4983230072969 + 3 ^ 40 * 2966493 * 2
def baseEnd_2966493 : Nat := 507745589066055772064951

theorem tailTrace_2966493 : CollatzResearch.WordTrace tailWord_2966493 prefixEnd_2966493 507745589066055772064951 := by
  unfold tailWord_2966493
  simp only [CollatzResearch.WordTrace]
  refine ⟨108196888441909972514104133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72131258961273315009402755 108196888441909972514104133)
  ·
    refine ⟨20286916582858119846394525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108196888441909972514104133 20286916582858119846394525)
    ·
      refine ⟨7607593718571794942397947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20286916582858119846394525 7607593718571794942397947)
      ·
        refine ⟨11411390577857692413596921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607593718571794942397947 11411390577857692413596921)
        ·
          refine ⟨8558542933393269310197691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11411390577857692413596921 8558542933393269310197691)
          ·
            refine ⟨12837814400089903965296537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8558542933393269310197691 12837814400089903965296537)
            ·
              refine ⟨9628360800067427973972403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12837814400089903965296537 9628360800067427973972403)
              ·
                refine ⟨14442541200101141960958605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9628360800067427973972403 14442541200101141960958605)
                ·
                  refine ⟨5415952950037928235359477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14442541200101141960958605 5415952950037928235359477)
                  ·
                    refine ⟨507745589066055772064951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5415952950037928235359477 507745589066055772064951)
                    ·
                      rfl

theorem cell23_2966493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2966493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966493 prefixEnd_2966493 := by exact prefixLift 2966493
  have htrace : WordTrace (prefixWord ++ tailWord_2966493) baseStart_2966493 baseEnd_2966493 := by
    simpa [prefixWord, tailWord_2966493, baseEnd_2966493] using wordTrace_append hprefix tailTrace_2966493
  have hstable : (prefixWord ++ tailWord_2966493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966493).length < 2 ^ (prefixWord ++ tailWord_2966493).sum := by decide
  have hdescent : baseEnd_2966493 < baseStart_2966493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966510 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_2966510 : Nat := 118140960795 + 2966510 * 2 ^ 59
def prefixEnd_2966510 : Nat := 4983230072969 + 3 ^ 40 * 2966510 * 2
def baseEnd_2966510 : Nat := 507748498789764583227425

theorem tailTrace_2966510 : CollatzResearch.WordTrace tailWord_2966510 prefixEnd_2966510 507748498789764583227425 := by
  unfold tailWord_2966510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524688560356048052184123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72131672321898922944981989 13524688560356048052184123)
  ·
    refine ⟨20287032840534072078276185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13524688560356048052184123 20287032840534072078276185)
    ·
      refine ⟨15215274630400554058707139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20287032840534072078276185 15215274630400554058707139)
      ·
        refine ⟨22822911945600831088060709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15215274630400554058707139 22822911945600831088060709)
        ·
          refine ⟨4279295989800155829011383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22822911945600831088060709 4279295989800155829011383)
          ·
            refine ⟨6418943984700233743517075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279295989800155829011383 6418943984700233743517075)
            ·
              refine ⟨9628415977050350615275613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418943984700233743517075 9628415977050350615275613)
              ·
                refine ⟨3610655991393881480728355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9628415977050350615275613 3610655991393881480728355)
                ·
                  refine ⟨5415983987090822221092533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610655991393881480728355 5415983987090822221092533)
                  ·
                    refine ⟨507748498789764583227425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5415983987090822221092533 507748498789764583227425)
                    ·
                      rfl

theorem cell23_2966510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_2966510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966510 prefixEnd_2966510 := by exact prefixLift 2966510
  have htrace : WordTrace (prefixWord ++ tailWord_2966510) baseStart_2966510 baseEnd_2966510 := by
    simpa [prefixWord, tailWord_2966510, baseEnd_2966510] using wordTrace_append hprefix tailTrace_2966510
  have hstable : (prefixWord ++ tailWord_2966510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966510).length < 2 ^ (prefixWord ++ tailWord_2966510).sum := by decide
  have hdescent : baseEnd_2966510 < baseStart_2966510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966567 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2966567 : Nat := 118140960795 + 2966567 * 2 ^ 59
def prefixEnd_2966567 : Nat := 4983230072969 + 3 ^ 40 * 2966567 * 2
def baseEnd_2966567 : Nat := 1523274764766600026669513

theorem tailTrace_2966567 : CollatzResearch.WordTrace tailWord_2966567 prefixEnd_2966567 1523274764766600026669513 := by
  unfold tailWord_2966567
  simp only [CollatzResearch.WordTrace]
  refine ⟨108199587443641883152297955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72133058295761255434865303 108199587443641883152297955)
  ·
    refine ⟨162299381165462824728446933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108199587443641883152297955 162299381165462824728446933)
    ·
      refine ⟨3803891746065534954572975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 162299381165462824728446933 3803891746065534954572975)
      ·
        refine ⟨5705837619098302431859463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803891746065534954572975 5705837619098302431859463)
        ·
          refine ⟨8558756428647453647789195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705837619098302431859463 8558756428647453647789195)
          ·
            refine ⟨12838134642971180471683793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8558756428647453647789195 12838134642971180471683793)
            ·
              refine ⟨9628600982228385353762845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12838134642971180471683793 9628600982228385353762845)
              ·
                refine ⟨3610725368335644507661067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9628600982228385353762845 3610725368335644507661067)
                ·
                  refine ⟨5416088052503466761491601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610725368335644507661067 5416088052503466761491601)
                  ·
                    refine ⟨4062066039377600071118701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5416088052503466761491601 4062066039377600071118701)
                    ·
                      refine ⟨1523274764766600026669513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062066039377600071118701 1523274764766600026669513)
                      ·
                        rfl

theorem cell23_2966567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2966567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966567 prefixEnd_2966567 := by exact prefixLift 2966567
  have htrace : WordTrace (prefixWord ++ tailWord_2966567) baseStart_2966567 baseEnd_2966567 := by
    simpa [prefixWord, tailWord_2966567, baseEnd_2966567] using wordTrace_append hprefix tailTrace_2966567
  have hstable : (prefixWord ++ tailWord_2966567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966567).length < 2 ^ (prefixWord ++ tailWord_2966567).sum := by decide
  have hdescent : baseEnd_2966567 < baseStart_2966567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966570 : List Nat := [3, 1, 4, 1, 4, 1, 9]
def baseStart_2966570 : Nat := 118140960795 + 2966570 * 2 ^ 59
def prefixEnd_2966570 : Nat := 4983230072969 + 3 ^ 40 * 2966570 * 2
def baseEnd_2966570 : Nat := 18805880311216833517679

theorem tailTrace_2966570 : CollatzResearch.WordTrace tailWord_2966570 prefixEnd_2966570 18805880311216833517679 := by
  unfold tailWord_2966570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27049924215657753666164291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72133131241754009776438109 27049924215657753666164291)
  ·
    refine ⟨40574886323486630499246437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27049924215657753666164291 40574886323486630499246437)
    ·
      refine ⟨7607791185653743218608707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40574886323486630499246437 7607791185653743218608707)
      ·
        refine ⟨11411686778480614827913061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607791185653743218608707 11411686778480614827913061)
        ·
          refine ⟨2139691270965115280233699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11411686778480614827913061 2139691270965115280233699)
          ·
            refine ⟨3209536906447672920350549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139691270965115280233699 3209536906447672920350549)
            ·
              refine ⟨18805880311216833517679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3209536906447672920350549 18805880311216833517679)
              ·
                rfl

theorem cell23_2966570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 9].length) (baseStart_2966570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966570 prefixEnd_2966570 := by exact prefixLift 2966570
  have htrace : WordTrace (prefixWord ++ tailWord_2966570) baseStart_2966570 baseEnd_2966570 := by
    simpa [prefixWord, tailWord_2966570, baseEnd_2966570] using wordTrace_append hprefix tailTrace_2966570
  have hstable : (prefixWord ++ tailWord_2966570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966570).length < 2 ^ (prefixWord ++ tailWord_2966570).sum := by decide
  have hdescent : baseEnd_2966570 < baseStart_2966570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966576 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_2966576 : Nat := 118140960795 + 2966576 * 2 ^ 59
def prefixEnd_2966576 : Nat := 4983230072969 + 3 ^ 40 * 2966576 * 2
def baseEnd_2966576 : Nat := 1523279386092490491456971

theorem tailTrace_2966576 : CollatzResearch.WordTrace tailWord_2966576 prefixEnd_2966576 1523279386092490491456971 := by
  unfold tailWord_2966576
  simp only [CollatzResearch.WordTrace]
  refine ⟨54099957850304638844687791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72133277133739518459583721 54099957850304638844687791)
  ·
    refine ⟨81149936775456958267031687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54099957850304638844687791 81149936775456958267031687)
    ·
      refine ⟨121724905163185437400547531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81149936775456958267031687 121724905163185437400547531)
      ·
        refine ⟨182587357744778156100821297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121724905163185437400547531 182587357744778156100821297)
        ·
          refine ⟨136940518308583617075615973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182587357744778156100821297 136940518308583617075615973)
          ·
            refine ⟨25676347182859428201677995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136940518308583617075615973 25676347182859428201677995)
            ·
              refine ⟨38514520774289142302516993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25676347182859428201677995 38514520774289142302516993)
              ·
                refine ⟨28885890580716856726887745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38514520774289142302516993 28885890580716856726887745)
                ·
                  refine ⟨21664417935537642545165809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28885890580716856726887745 21664417935537642545165809)
                  ·
                    refine ⟨16248313451653231908874357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21664417935537642545165809 16248313451653231908874357)
                    ·
                      refine ⟨1523279386092490491456971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16248313451653231908874357 1523279386092490491456971)
                      ·
                        rfl

theorem cell23_2966576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_2966576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966576 prefixEnd_2966576 := by exact prefixLift 2966576
  have htrace : WordTrace (prefixWord ++ tailWord_2966576) baseStart_2966576 baseEnd_2966576 := by
    simpa [prefixWord, tailWord_2966576, baseEnd_2966576] using wordTrace_append hprefix tailTrace_2966576
  have hstable : (prefixWord ++ tailWord_2966576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966576).length < 2 ^ (prefixWord ++ tailWord_2966576).sum := by decide
  have hdescent : baseEnd_2966576 < baseStart_2966576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966597 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 2, 1, 3]
def baseStart_2966597 : Nat := 118140960795 + 2966597 * 2 ^ 59
def prefixEnd_2966597 : Nat := 4983230072969 + 3 ^ 40 * 2966597 * 2
def baseEnd_2966597 : Nat := 1523290169186234909294375

theorem tailTrace_2966597 : CollatzResearch.WordTrace tailWord_2966597 prefixEnd_2966597 1523290169186234909294375 := by
  unfold tailWord_2966597
  simp only [CollatzResearch.WordTrace]
  refine ⟨108200681633533198275890045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72133787755688798850593363 108200681633533198275890045)
  ·
    refine ⟨40575255612574949353458767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108200681633533198275890045 40575255612574949353458767)
    ·
      refine ⟨60862883418862424030188151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40575255612574949353458767 60862883418862424030188151)
      ·
        refine ⟨91294325128293636045282227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60862883418862424030188151 91294325128293636045282227)
        ·
          refine ⟨136941487692440454067923341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91294325128293636045282227 136941487692440454067923341)
          ·
            refine ⟨51353057884665170275471253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136941487692440454067923341 51353057884665170275471253)
            ·
              refine ⟨2407174588343679856662715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51353057884665170275471253 2407174588343679856662715)
              ·
                refine ⟨3610761882515519784994073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407174588343679856662715 3610761882515519784994073)
                ·
                  refine ⟨2708071411886639838745555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610761882515519784994073 2708071411886639838745555)
                  ·
                    refine ⟨4062107117829959758118333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708071411886639838745555 4062107117829959758118333)
                    ·
                      refine ⟨1523290169186234909294375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062107117829959758118333 1523290169186234909294375)
                      ·
                        rfl

theorem cell23_2966597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_2966597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966597 prefixEnd_2966597 := by exact prefixLift 2966597
  have htrace : WordTrace (prefixWord ++ tailWord_2966597) baseStart_2966597 baseEnd_2966597 := by
    simpa [prefixWord, tailWord_2966597, baseEnd_2966597] using wordTrace_append hprefix tailTrace_2966597
  have hstable : (prefixWord ++ tailWord_2966597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966597).length < 2 ^ (prefixWord ++ tailWord_2966597).sum := by decide
  have hdescent : baseEnd_2966597 < baseStart_2966597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966614 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2966614 : Nat := 118140960795 + 2966614 * 2 ^ 59
def prefixEnd_2966614 : Nat := 4983230072969 + 3 ^ 40 * 2966614 * 2
def baseEnd_2966614 : Nat := 1523298898357361342781797

theorem tailTrace_2966614 : CollatzResearch.WordTrace tailWord_2966614 prefixEnd_2966614 1523298898357361342781797 := by
  unfold tailWord_2966614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762581354654475636203681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72134201116314406786172597 6762581354654475636203681)
  ·
    refine ⟨5071936015990856727152761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6762581354654475636203681 5071936015990856727152761)
    ·
      refine ⟨3803952011993142545364571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5071936015990856727152761 3803952011993142545364571)
      ·
        refine ⟨5705928017989713818046857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803952011993142545364571 5705928017989713818046857)
        ·
          refine ⟨4279446013492285363535143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5705928017989713818046857 4279446013492285363535143)
          ·
            refine ⟨6419169020238428045302715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279446013492285363535143 6419169020238428045302715)
            ·
              refine ⟨9628753530357642067954073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419169020238428045302715 9628753530357642067954073)
              ·
                refine ⟨7221565147768231550965555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9628753530357642067954073 7221565147768231550965555)
                ·
                  refine ⟨10832347721652347326448333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7221565147768231550965555 10832347721652347326448333)
                  ·
                    refine ⟨4062130395619630247418125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10832347721652347326448333 4062130395619630247418125)
                    ·
                      refine ⟨1523298898357361342781797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062130395619630247418125 1523298898357361342781797)
                      ·
                        rfl

theorem cell23_2966614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2966614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966614 prefixEnd_2966614 := by exact prefixLift 2966614
  have htrace : WordTrace (prefixWord ++ tailWord_2966614) baseStart_2966614 baseEnd_2966614 := by
    simpa [prefixWord, tailWord_2966614, baseEnd_2966614] using wordTrace_append hprefix tailTrace_2966614
  have hstable : (prefixWord ++ tailWord_2966614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966614).length < 2 ^ (prefixWord ++ tailWord_2966614).sum := by decide
  have hdescent : baseEnd_2966614 < baseStart_2966614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966730 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_2966730 : Nat := 118140960795 + 2966730 * 2 ^ 59
def prefixEnd_2966730 : Nat := 4983230072969 + 3 ^ 40 * 2966730 * 2
def baseEnd_2966730 : Nat := 1523358462113282888931263

theorem tailTrace_2966730 : CollatzResearch.WordTrace tailWord_2966730 prefixEnd_2966730 1523358462113282888931263 := by
  unfold tailWord_2966730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27051383135512840497620411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72137021694700907993654429 27051383135512840497620411)
  ·
    refine ⟨40577074703269260746430617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27051383135512840497620411 40577074703269260746430617)
    ·
      refine ⟨30432806027451945559822963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40577074703269260746430617 30432806027451945559822963)
      ·
        refine ⟨45649209041177918339734445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30432806027451945559822963 45649209041177918339734445)
        ·
          refine ⟨17118453390441719377400417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45649209041177918339734445 17118453390441719377400417)
          ·
            refine ⟨12838840042831289533050313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17118453390441719377400417 12838840042831289533050313)
            ·
              refine ⟨9629130032123467149787735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12838840042831289533050313 9629130032123467149787735)
              ·
                refine ⟨14443695048185200724681603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9629130032123467149787735 14443695048185200724681603)
                ·
                  refine ⟨21665542572277801087022405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14443695048185200724681603 21665542572277801087022405)
                  ·
                    refine ⟨4062289232302087703816701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21665542572277801087022405 4062289232302087703816701)
                    ·
                      refine ⟨1523358462113282888931263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062289232302087703816701 1523358462113282888931263)
                      ·
                        rfl

theorem cell23_2966730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_2966730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966730 prefixEnd_2966730 := by exact prefixLift 2966730
  have htrace : WordTrace (prefixWord ++ tailWord_2966730) baseStart_2966730 baseEnd_2966730 := by
    simpa [prefixWord, tailWord_2966730, baseEnd_2966730] using wordTrace_append hprefix tailTrace_2966730
  have hstable : (prefixWord ++ tailWord_2966730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966730).length < 2 ^ (prefixWord ++ tailWord_2966730).sum := by decide
  have hdescent : baseEnd_2966730 < baseStart_2966730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966787 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 2, 3, 2]
def baseStart_2966787 : Nat := 118140960795 + 2966787 * 2 ^ 59
def prefixEnd_2966787 : Nat := 4983230072969 + 3 ^ 40 * 2966787 * 2
def baseEnd_2966787 : Nat := 1523387730510589165918501

theorem tailTrace_2966787 : CollatzResearch.WordTrace tailWord_2966787 prefixEnd_2966787 1523387730510589165918501 := by
  unfold tailWord_2966787
  simp only [CollatzResearch.WordTrace]
  refine ⟨108207611502844860725306615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72138407668563240483537743 108207611502844860725306615)
  ·
    refine ⟨162311417254267291087959923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108207611502844860725306615 162311417254267291087959923)
    ·
      refine ⟨243467125881400936631939885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162311417254267291087959923 243467125881400936631939885)
      ·
        refine ⟨91300172205525351236977457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243467125881400936631939885 91300172205525351236977457)
        ·
          refine ⟨68475129154144013427733093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91300172205525351236977457 68475129154144013427733093)
          ·
            refine ⟨12839086716402002517699955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68475129154144013427733093 12839086716402002517699955)
            ·
              refine ⟨19258630074603003776549933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12839086716402002517699955 19258630074603003776549933)
              ·
                refine ⟨7221986277976126416206225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19258630074603003776549933 7221986277976126416206225)
                ·
                  refine ⟨5416489708482094812154669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7221986277976126416206225 5416489708482094812154669)
                  ·
                    refine ⟨2031183640680785554558001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5416489708482094812154669 2031183640680785554558001)
                    ·
                      refine ⟨1523387730510589165918501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031183640680785554558001 1523387730510589165918501)
                      ·
                        rfl

theorem cell23_2966787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_2966787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966787 prefixEnd_2966787 := by exact prefixLift 2966787
  have htrace : WordTrace (prefixWord ++ tailWord_2966787) baseStart_2966787 baseEnd_2966787 := by
    simpa [prefixWord, tailWord_2966787, baseEnd_2966787] using wordTrace_append hprefix tailTrace_2966787
  have hstable : (prefixWord ++ tailWord_2966787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966787).length < 2 ^ (prefixWord ++ tailWord_2966787).sum := by decide
  have hdescent : baseEnd_2966787 < baseStart_2966787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966794 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_2966794 : Nat := 118140960795 + 2966794 * 2 ^ 59
def prefixEnd_2966794 : Nat := 4983230072969 + 3 ^ 40 * 2966794 * 2
def baseEnd_2966794 : Nat := 1523391324875170638530969

theorem tailTrace_2966794 : CollatzResearch.WordTrace tailWord_2966794 prefixEnd_2966794 1523391324875170638530969 := by
  unfold tailWord_2966794
  simp only [CollatzResearch.WordTrace]
  refine ⟨27051966703454875230202859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72138577875879667280540957 27051966703454875230202859)
  ·
    refine ⟨40577950055182312845304289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27051966703454875230202859 40577950055182312845304289)
    ·
      refine ⟨30433462541386734633978217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40577950055182312845304289 30433462541386734633978217)
      ·
        refine ⟨22825096906040050975483663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30433462541386734633978217 22825096906040050975483663)
        ·
          refine ⟨34237645359060076463225495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22825096906040050975483663 34237645359060076463225495)
          ·
            refine ⟨51356468038590114694838243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34237645359060076463225495 51356468038590114694838243)
            ·
              refine ⟨77034702057885172042257365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51356468038590114694838243 77034702057885172042257365)
              ·
                refine ⟨1805500829481683719740407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77034702057885172042257365 1805500829481683719740407)
                ·
                  refine ⟨2708251244222525579610611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805500829481683719740407 2708251244222525579610611)
                  ·
                    refine ⟨4062376866333788369415917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708251244222525579610611 4062376866333788369415917)
                    ·
                      refine ⟨1523391324875170638530969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062376866333788369415917 1523391324875170638530969)
                      ·
                        rfl

theorem cell23_2966794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_2966794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966794 prefixEnd_2966794 := by exact prefixLift 2966794
  have htrace : WordTrace (prefixWord ++ tailWord_2966794) baseStart_2966794 baseEnd_2966794 := by
    simpa [prefixWord, tailWord_2966794, baseEnd_2966794] using wordTrace_append hprefix tailTrace_2966794
  have hstable : (prefixWord ++ tailWord_2966794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966794).length < 2 ^ (prefixWord ++ tailWord_2966794).sum := by decide
  have hdescent : baseEnd_2966794 < baseStart_2966794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 6, 2]
def baseStart_2966800 : Nat := 118140960795 + 2966800 * 2 ^ 59
def prefixEnd_2966800 : Nat := 4983230072969 + 3 ^ 40 * 2966800 * 2
def baseEnd_2966800 : Nat := 1523394405759097615055941

theorem tailTrace_2966800 : CollatzResearch.WordTrace tailWord_2966800 prefixEnd_2966800 1523394405759097615055941 := by
  unfold tailWord_2966800
  simp only [CollatzResearch.WordTrace]
  refine ⟨54104042825898881972764927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72138723767865175963686569 54104042825898881972764927)
  ·
    refine ⟨81156064238848322959147391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54104042825898881972764927 81156064238848322959147391)
    ·
      refine ⟨121734096358272484438721087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81156064238848322959147391 121734096358272484438721087)
      ·
        refine ⟨182601144537408726658081631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121734096358272484438721087 182601144537408726658081631)
        ·
          refine ⟨273901716806113089987122447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182601144537408726658081631 273901716806113089987122447)
          ·
            refine ⟨410852575209169634980683671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273901716806113089987122447 410852575209169634980683671)
            ·
              refine ⟨616278862813754452471025507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410852575209169634980683671 616278862813754452471025507)
              ·
                refine ⟨924418294220631678706538261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616278862813754452471025507 924418294220631678706538261)
                ·
                  refine ⟨43332107541592109939368981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 924418294220631678706538261 43332107541592109939368981)
                  ·
                    refine ⟨2031192541012130153407921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43332107541592109939368981 2031192541012130153407921)
                    ·
                      refine ⟨1523394405759097615055941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031192541012130153407921 1523394405759097615055941)
                      ·
                        rfl

theorem cell23_2966800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 6, 2].length) (baseStart_2966800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966800 prefixEnd_2966800 := by exact prefixLift 2966800
  have htrace : WordTrace (prefixWord ++ tailWord_2966800) baseStart_2966800 baseEnd_2966800 := by
    simpa [prefixWord, tailWord_2966800, baseEnd_2966800] using wordTrace_append hprefix tailTrace_2966800
  have hstable : (prefixWord ++ tailWord_2966800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966800).length < 2 ^ (prefixWord ++ tailWord_2966800).sum := by decide
  have hdescent : baseEnd_2966800 < baseStart_2966800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966820 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2966820 : Nat := 118140960795 + 2966820 * 2 ^ 59
def prefixEnd_2966820 : Nat := 4983230072969 + 3 ^ 40 * 2966820 * 2
def baseEnd_2966820 : Nat := 1523404675372187536805849

theorem tailTrace_2966820 : CollatzResearch.WordTrace tailWord_2966820 prefixEnd_2966820 1523404675372187536805849 := by
  unfold tailWord_2966820
  simp only [CollatzResearch.WordTrace]
  refine ⟨54104407555862653680628957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72139210074483538240838609 54104407555862653680628957)
  ·
    refine ⟨20289152833448495130235859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54104407555862653680628957 20289152833448495130235859)
    ·
      refine ⟨30433729250172742695353789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20289152833448495130235859 30433729250172742695353789)
      ·
        refine ⟨11412648468814778510757671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30433729250172742695353789 11412648468814778510757671)
        ·
          refine ⟨17118972703222167766136507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11412648468814778510757671 17118972703222167766136507)
          ·
            refine ⟨25678459054833251649204761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17118972703222167766136507 25678459054833251649204761)
            ·
              refine ⟨19258844291124938736903571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25678459054833251649204761 19258844291124938736903571)
              ·
                refine ⟨28888266436687408105355357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19258844291124938736903571 28888266436687408105355357)
                ·
                  refine ⟨10833099913757778039508259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28888266436687408105355357 10833099913757778039508259)
                  ·
                    refine ⟨16249649870636667059262389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10833099913757778039508259 16249649870636667059262389)
                    ·
                      refine ⟨1523404675372187536805849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16249649870636667059262389 1523404675372187536805849)
                      ·
                        rfl

theorem cell23_2966820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2966820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966820 prefixEnd_2966820 := by exact prefixLift 2966820
  have htrace : WordTrace (prefixWord ++ tailWord_2966820) baseStart_2966820 baseEnd_2966820 := by
    simpa [prefixWord, tailWord_2966820, baseEnd_2966820] using wordTrace_append hprefix tailTrace_2966820
  have hstable : (prefixWord ++ tailWord_2966820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966820).length < 2 ^ (prefixWord ++ tailWord_2966820).sum := by decide
  have hdescent : baseEnd_2966820 < baseStart_2966820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966834 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_2966834 : Nat := 118140960795 + 2966834 * 2 ^ 59
def prefixEnd_2966834 : Nat := 4983230072969 + 3 ^ 40 * 2966834 * 2
def baseEnd_2966834 : Nat := 1523411864101350482030785

theorem tailTrace_2966834 : CollatzResearch.WordTrace tailWord_2966834 prefixEnd_2966834 1523411864101350482030785 := by
  unfold tailWord_2966834
  simp only [CollatzResearch.WordTrace]
  refine ⟨27052331433418646938066889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72139550489116391834845037 27052331433418646938066889)
  ·
    refine ⟨20289248575063985203550167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27052331433418646938066889 20289248575063985203550167)
    ·
      refine ⟨30433872862595977805325251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20289248575063985203550167 30433872862595977805325251)
      ·
        refine ⟨45650809293893966707987877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30433872862595977805325251 45650809293893966707987877)
        ·
          refine ⟨8559526742605118757747727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45650809293893966707987877 8559526742605118757747727)
          ·
            refine ⟨12839290113907678136621591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8559526742605118757747727 12839290113907678136621591)
            ·
              refine ⟨19258935170861517204932387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12839290113907678136621591 19258935170861517204932387)
              ·
                refine ⟨28888402756292275807398581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19258935170861517204932387 28888402756292275807398581)
                ·
                  refine ⟨2708287758402400856943617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28888402756292275807398581 2708287758402400856943617)
                  ·
                    refine ⟨2031215818801800642707713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2708287758402400856943617 2031215818801800642707713)
                    ·
                      refine ⟨1523411864101350482030785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031215818801800642707713 1523411864101350482030785)
                      ·
                        rfl

theorem cell23_2966834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_2966834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966834 prefixEnd_2966834 := by exact prefixLift 2966834
  have htrace : WordTrace (prefixWord ++ tailWord_2966834) baseStart_2966834 baseEnd_2966834 := by
    simpa [prefixWord, tailWord_2966834, baseEnd_2966834] using wordTrace_append hprefix tailTrace_2966834
  have hstable : (prefixWord ++ tailWord_2966834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966834).length < 2 ^ (prefixWord ++ tailWord_2966834).sum := by decide
  have hdescent : baseEnd_2966834 < baseStart_2966834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966837 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2966837 : Nat := 118140960795 + 2966837 * 2 ^ 59
def prefixEnd_2966837 : Nat := 4983230072969 + 3 ^ 40 * 2966837 * 2
def baseEnd_2966837 : Nat := 1523413404543313970293271

theorem tailTrace_2966837 : CollatzResearch.WordTrace tailWord_2966837 prefixEnd_2966837 1523413404543313970293271 := by
  unfold tailWord_2966837
  simp only [CollatzResearch.WordTrace]
  refine ⟨108209435152663719264626765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72139623435109146176417843 108209435152663719264626765)
  ·
    refine ⟨40578538182248894724235037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108209435152663719264626765 40578538182248894724235037)
    ·
      refine ⟨15216951818343335521588139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40578538182248894724235037 15216951818343335521588139)
      ·
        refine ⟨22825427727515003282382209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15216951818343335521588139 22825427727515003282382209)
        ·
          refine ⟨17119070795636252461786657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22825427727515003282382209 17119070795636252461786657)
          ·
            refine ⟨12839303096727189346339993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17119070795636252461786657 12839303096727189346339993)
            ·
              refine ⟨9629477322545392009754995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12839303096727189346339993 9629477322545392009754995)
              ·
                refine ⟨14444215983818088014632493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9629477322545392009754995 14444215983818088014632493)
                ·
                  refine ⟨5416580993931783005487185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14444215983818088014632493 5416580993931783005487185)
                  ·
                    refine ⟨4062435745448837254115389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5416580993931783005487185 4062435745448837254115389)
                    ·
                      refine ⟨1523413404543313970293271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062435745448837254115389 1523413404543313970293271)
                      ·
                        rfl

theorem cell23_2966837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2966837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966837 prefixEnd_2966837 := by exact prefixLift 2966837
  have htrace : WordTrace (prefixWord ++ tailWord_2966837) baseStart_2966837 baseEnd_2966837 := by
    simpa [prefixWord, tailWord_2966837, baseEnd_2966837] using wordTrace_append hprefix tailTrace_2966837
  have hstable : (prefixWord ++ tailWord_2966837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966837).length < 2 ^ (prefixWord ++ tailWord_2966837).sum := by decide
  have hdescent : baseEnd_2966837 < baseStart_2966837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966843 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_2966843 : Nat := 118140960795 + 2966843 * 2 ^ 59
def prefixEnd_2966843 : Nat := 4983230072969 + 3 ^ 40 * 2966843 * 2
def baseEnd_2966843 : Nat := 1523416485427240946818243

theorem tailTrace_2966843 : CollatzResearch.WordTrace tailWord_2966843 prefixEnd_2966843 1523416485427240946818243 := by
  unfold tailWord_2966843
  simp only [CollatzResearch.WordTrace]
  refine ⟨108209653990641982289345183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72139769327094654859563455 108209653990641982289345183)
  ·
    refine ⟨162314480985962973434017775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108209653990641982289345183 162314480985962973434017775)
    ·
      refine ⟨243471721478944460151026663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162314480985962973434017775 243471721478944460151026663)
      ·
        refine ⟨365207582218416690226539995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243471721478944460151026663 365207582218416690226539995)
        ·
          refine ⟨547811373327625035339809993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365207582218416690226539995 547811373327625035339809993)
          ·
            refine ⟨410858529995718776504857495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547811373327625035339809993 410858529995718776504857495)
            ·
              refine ⟨616287794993578164757286243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410858529995718776504857495 616287794993578164757286243)
              ·
                refine ⟨924431692490367247135929365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616287794993578164757286243 924431692490367247135929365)
                ·
                  refine ⟨43332735585485964709496689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 924431692490367247135929365 43332735585485964709496689)
                  ·
                    refine ⟨32499551689114473532122517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43332735585485964709496689 32499551689114473532122517)
                    ·
                      refine ⟨1523416485427240946818243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32499551689114473532122517 1523416485427240946818243)
                      ·
                        rfl

theorem cell23_2966843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_2966843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966843 prefixEnd_2966843 := by exact prefixLift 2966843
  have htrace : WordTrace (prefixWord ++ tailWord_2966843) baseStart_2966843 baseEnd_2966843 := by
    simpa [prefixWord, tailWord_2966843, baseEnd_2966843] using wordTrace_append hprefix tailTrace_2966843
  have hstable : (prefixWord ++ tailWord_2966843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966843).length < 2 ^ (prefixWord ++ tailWord_2966843).sum := by decide
  have hdescent : baseEnd_2966843 < baseStart_2966843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966861 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2966861 : Nat := 118140960795 + 2966861 * 2 ^ 59
def prefixEnd_2966861 : Nat := 4983230072969 + 3 ^ 40 * 2966861 * 2
def baseEnd_2966861 : Nat := 507808576026340625464387

theorem tailTrace_2966861 : CollatzResearch.WordTrace tailWord_2966861 prefixEnd_2966861 507808576026340625464387 := by
  unfold tailWord_2966861
  simp only [CollatzResearch.WordTrace]
  refine ⟨108210310504576771363500437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72140207003051180909000291 108210310504576771363500437)
  ·
    refine ⟨5072358304902036157664083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108210310504576771363500437 5072358304902036157664083)
    ·
      refine ⟨7608537457353054236496125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5072358304902036157664083 7608537457353054236496125)
      ·
        refine ⟨2853201546507395338686047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7608537457353054236496125 2853201546507395338686047)
        ·
          refine ⟨4279802319761093008029071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853201546507395338686047 4279802319761093008029071)
          ·
            refine ⟨6419703479641639512043607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279802319761093008029071 6419703479641639512043607)
            ·
              refine ⟨9629555219462459268065411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419703479641639512043607 9629555219462459268065411)
              ·
                refine ⟨14444332829193688902098117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9629555219462459268065411 14444332829193688902098117)
                ·
                  refine ⟨2708312405473816669143397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14444332829193688902098117 2708312405473816669143397)
                  ·
                    refine ⟨507808576026340625464387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708312405473816669143397 507808576026340625464387)
                    ·
                      rfl

theorem cell23_2966861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2966861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966861 prefixEnd_2966861 := by exact prefixLift 2966861
  have htrace : WordTrace (prefixWord ++ tailWord_2966861) baseStart_2966861 baseEnd_2966861 := by
    simpa [prefixWord, tailWord_2966861, baseEnd_2966861] using wordTrace_append hprefix tailTrace_2966861
  have hstable : (prefixWord ++ tailWord_2966861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966861).length < 2 ^ (prefixWord ++ tailWord_2966861).sum := by decide
  have hdescent : baseEnd_2966861 < baseStart_2966861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966867 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 3]
def baseStart_2966867 : Nat := 118140960795 + 2966867 * 2 ^ 59
def prefixEnd_2966867 : Nat := 4983230072969 + 3 ^ 40 * 2966867 * 2
def baseEnd_2966867 : Nat := 1523428808962948852918133

theorem tailTrace_2966867 : CollatzResearch.WordTrace tailWord_2966867 prefixEnd_2966867 1523428808962948852918133 := by
  unfold tailWord_2966867
  simp only [CollatzResearch.WordTrace]
  refine ⟨108210529342555034388218855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72140352895036689592145903 108210529342555034388218855)
  ·
    refine ⟨162315794013832551582328283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108210529342555034388218855 162315794013832551582328283)
    ·
      refine ⟨243473691020748827373492425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162315794013832551582328283 243473691020748827373492425)
      ·
        refine ⟨182605268265561620530119319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243473691020748827373492425 182605268265561620530119319)
        ·
          refine ⟨273907902398342430795178979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182605268265561620530119319 273907902398342430795178979)
          ·
            refine ⟨410861853597513646192768469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273907902398342430795178979 410861853597513646192768469)
            ·
              refine ⟨9629574693691726082643011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 410861853597513646192768469 9629574693691726082643011)
              ·
                refine ⟨14444362040537589123964517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9629574693691726082643011 14444362040537589123964517)
                ·
                  refine ⟨2708317882600797960743347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14444362040537589123964517 2708317882600797960743347)
                  ·
                    refine ⟨4062476823901196941115021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708317882600797960743347 4062476823901196941115021)
                    ·
                      refine ⟨1523428808962948852918133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062476823901196941115021 1523428808962948852918133)
                      ·
                        rfl

theorem cell23_2966867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_2966867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966867 prefixEnd_2966867 := by exact prefixLift 2966867
  have htrace : WordTrace (prefixWord ++ tailWord_2966867) baseStart_2966867 baseEnd_2966867 := by
    simpa [prefixWord, tailWord_2966867, baseEnd_2966867] using wordTrace_append hprefix tailTrace_2966867
  have hstable : (prefixWord ++ tailWord_2966867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966867).length < 2 ^ (prefixWord ++ tailWord_2966867).sum := by decide
  have hdescent : baseEnd_2966867 < baseStart_2966867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966884 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_2966884 : Nat := 118140960795 + 2966884 * 2 ^ 59
def prefixEnd_2966884 : Nat := 4983230072969 + 3 ^ 40 * 2966884 * 2
def baseEnd_2966884 : Nat := 1523437538134075286405555

theorem tailTrace_2966884 : CollatzResearch.WordTrace tailWord_2966884 prefixEnd_2966884 1523437538134075286405555 := by
  unfold tailWord_2966884
  simp only [CollatzResearch.WordTrace]
  refine ⟨54105574691746723145793853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72140766255662297527725137 54105574691746723145793853)
  ·
    refine ⟨20289590509405021179672695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54105574691746723145793853 20289590509405021179672695)
    ·
      refine ⟨30434385764107531769509043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20289590509405021179672695 30434385764107531769509043)
      ·
        refine ⟨45651578646161297654263565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30434385764107531769509043 45651578646161297654263565)
        ·
          refine ⟨17119341992310486620348837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45651578646161297654263565 17119341992310486620348837)
          ·
            refine ⟨3209876623558216241315407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17119341992310486620348837 3209876623558216241315407)
            ·
              refine ⟨4814814935337324361973111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209876623558216241315407 4814814935337324361973111)
              ·
                refine ⟨7222222403005986542959667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4814814935337324361973111 7222222403005986542959667)
                ·
                  refine ⟨10833333604508979814439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7222222403005986542959667 10833333604508979814439501)
                  ·
                    refine ⟨4062500101690867430414813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10833333604508979814439501 4062500101690867430414813)
                    ·
                      refine ⟨1523437538134075286405555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062500101690867430414813 1523437538134075286405555)
                      ·
                        rfl

theorem cell23_2966884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_2966884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966884 prefixEnd_2966884 := by exact prefixLift 2966884
  have htrace : WordTrace (prefixWord ++ tailWord_2966884) baseStart_2966884 baseEnd_2966884 := by
    simpa [prefixWord, tailWord_2966884, baseEnd_2966884] using wordTrace_append hprefix tailTrace_2966884
  have hstable : (prefixWord ++ tailWord_2966884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966884).length < 2 ^ (prefixWord ++ tailWord_2966884).sum := by decide
  have hdescent : baseEnd_2966884 < baseStart_2966884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966907 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 3, 4, 2]
def baseStart_2966907 : Nat := 118140960795 + 2966907 * 2 ^ 59
def prefixEnd_2966907 : Nat := 4983230072969 + 3 ^ 40 * 2966907 * 2
def baseEnd_2966907 : Nat := 1523449348189128696417949

theorem tailTrace_2966907 : CollatzResearch.WordTrace tailWord_2966907 prefixEnd_2966907 1523449348189128696417949 := by
  unfold tailWord_2966907
  simp only [CollatzResearch.WordTrace]
  refine ⟨108211988262410121219674975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72141325508273414146449983 108211988262410121219674975)
  ·
    refine ⟨162317982393615181829512463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108211988262410121219674975 162317982393615181829512463)
    ·
      refine ⟨243476973590422772744268695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162317982393615181829512463 243476973590422772744268695)
      ·
        refine ⟨365215460385634159116403043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243476973590422772744268695 365215460385634159116403043)
        ·
          refine ⟨547823190578451238674604565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365215460385634159116403043 547823190578451238674604565)
          ·
            refine ⟨25679212058364901812872089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 547823190578451238674604565 25679212058364901812872089)
            ·
              refine ⟨19259409043773676359654067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25679212058364901812872089 19259409043773676359654067)
              ·
                refine ⟨28889113565660514539481101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19259409043773676359654067 28889113565660514539481101)
                ·
                  refine ⟨10833417587122692952305413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28889113565660514539481101 10833417587122692952305413)
                  ·
                    refine ⟨2031265797585504928557265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10833417587122692952305413 2031265797585504928557265)
                    ·
                      refine ⟨1523449348189128696417949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031265797585504928557265 1523449348189128696417949)
                      ·
                        rfl

theorem cell23_2966907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4, 2].length) (baseStart_2966907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966907 prefixEnd_2966907 := by exact prefixLift 2966907
  have htrace : WordTrace (prefixWord ++ tailWord_2966907) baseStart_2966907 baseEnd_2966907 := by
    simpa [prefixWord, tailWord_2966907, baseEnd_2966907] using wordTrace_append hprefix tailTrace_2966907
  have hstable : (prefixWord ++ tailWord_2966907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966907).length < 2 ^ (prefixWord ++ tailWord_2966907).sum := by decide
  have hdescent : baseEnd_2966907 < baseStart_2966907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966924 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 4, 2, 2]
def baseStart_2966924 : Nat := 118140960795 + 2966924 * 2 ^ 59
def prefixEnd_2966924 : Nat := 4983230072969 + 3 ^ 40 * 2966924 * 2
def baseEnd_2966924 : Nat := 1523458077360255129905371

theorem tailTrace_2966924 : CollatzResearch.WordTrace tailWord_2966924 prefixEnd_2966924 1523458077360255129905371 := by
  unfold tailWord_2966924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54106304151674266561521913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72141738868899022082029217 54106304151674266561521913)
  ·
    refine ⟨40579728113755699921141435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54106304151674266561521913 40579728113755699921141435)
    ·
      refine ⟨60869592170633549881712153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40579728113755699921141435 60869592170633549881712153)
      ·
        refine ⟨45652194127975162411284115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60869592170633549881712153 45652194127975162411284115)
        ·
          refine ⟨68478291191962743616926173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45652194127975162411284115 68478291191962743616926173)
          ·
            refine ⟨25679359196986028856347315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68478291191962743616926173 25679359196986028856347315)
            ·
              refine ⟨38519038795479043284520973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25679359196986028856347315 38519038795479043284520973)
              ·
                refine ⟨14444639548304641231695365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38519038795479043284520973 14444639548304641231695365)
                ·
                  refine ⟨2708369915307120230942881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14444639548304641231695365 2708369915307120230942881)
                  ·
                    refine ⟨2031277436480340173207161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2708369915307120230942881 2031277436480340173207161)
                    ·
                      refine ⟨1523458077360255129905371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031277436480340173207161 1523458077360255129905371)
                      ·
                        rfl

theorem cell23_2966924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_2966924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966924 prefixEnd_2966924 := by exact prefixLift 2966924
  have htrace : WordTrace (prefixWord ++ tailWord_2966924) baseStart_2966924 baseEnd_2966924 := by
    simpa [prefixWord, tailWord_2966924, baseEnd_2966924] using wordTrace_append hprefix tailTrace_2966924
  have hstable : (prefixWord ++ tailWord_2966924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966924).length < 2 ^ (prefixWord ++ tailWord_2966924).sum := by decide
  have hdescent : baseEnd_2966924 < baseStart_2966924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966997 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2966997 : Nat := 118140960795 + 2966997 * 2 ^ 59
def prefixEnd_2966997 : Nat := 4983230072969 + 3 ^ 40 * 2966997 * 2
def baseEnd_2966997 : Nat := 1523495561448033344292535

theorem tailTrace_2966997 : CollatzResearch.WordTrace tailWord_2966997 prefixEnd_2966997 1523495561448033344292535 := by
  unfold tailWord_2966997
  simp only [CollatzResearch.WordTrace]
  refine ⟨108215270832084066590451245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72143513888056044393634163 108215270832084066590451245)
  ·
    refine ⟨40580726562031524971419217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108215270832084066590451245 40580726562031524971419217)
    ·
      refine ⟨30435544921523643728564413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40580726562031524971419217 30435544921523643728564413)
      ·
        refine ⟨11413329345571366398211655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30435544921523643728564413 11413329345571366398211655)
        ·
          refine ⟨17119994018357049597317483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11413329345571366398211655 17119994018357049597317483)
          ·
            refine ⟨25679991027535574395976225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17119994018357049597317483 25679991027535574395976225)
            ·
              refine ⟨19259993270651680796982169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25679991027535574395976225 19259993270651680796982169)
              ·
                refine ⟨14444994952988760597736627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19259993270651680796982169 14444994952988760597736627)
                ·
                  refine ⟨21667492429483140896604941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14444994952988760597736627 21667492429483140896604941)
                  ·
                    refine ⟨8125309661056177836226853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21667492429483140896604941 8125309661056177836226853)
                    ·
                      refine ⟨1523495561448033344292535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8125309661056177836226853 1523495561448033344292535)
                      ·
                        rfl

theorem cell23_2966997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2966997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2966997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2966997 prefixEnd_2966997 := by exact prefixLift 2966997
  have htrace : WordTrace (prefixWord ++ tailWord_2966997) baseStart_2966997 baseEnd_2966997 := by
    simpa [prefixWord, tailWord_2966997, baseEnd_2966997] using wordTrace_append hprefix tailTrace_2966997
  have hstable : (prefixWord ++ tailWord_2966997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966997).length < 2 ^ (prefixWord ++ tailWord_2966997).sum := by decide
  have hdescent : baseEnd_2966997 < baseStart_2966997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967037 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 8]
def baseStart_2967037 : Nat := 118140960795 + 2967037 * 2 ^ 59
def prefixEnd_2967037 : Nat := 4983230072969 + 3 ^ 40 * 2967037 * 2
def baseEnd_2967037 : Nat := 169279566741579243088039

theorem tailTrace_2967037 : CollatzResearch.WordTrace tailWord_2967037 prefixEnd_2967037 169279566741579243088039 := by
  unfold tailWord_2967037
  simp only [CollatzResearch.WordTrace]
  refine ⟨108216729751939153421907365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72144486501292768947938243 108216729751939153421907365)
  ·
    refine ⟨20290636828488591266607631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108216729751939153421907365 20290636828488591266607631)
    ·
      refine ⟨30435955242732886899911447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20290636828488591266607631 30435955242732886899911447)
      ·
        refine ⟨45653932864099330349867171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30435955242732886899911447 45653932864099330349867171)
        ·
          refine ⟨68480899296148995524800757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45653932864099330349867171 68480899296148995524800757)
          ·
            refine ⟨6420084309013968330450071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68480899296148995524800757 6420084309013968330450071)
            ·
              refine ⟨9630126463520952495675107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6420084309013968330450071 9630126463520952495675107)
              ·
                refine ⟨14445189695281428743512661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9630126463520952495675107 14445189695281428743512661)
                ·
                  refine ⟨169279566741579243088039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14445189695281428743512661 169279566741579243088039)
                  ·
                    rfl

theorem cell23_2967037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_2967037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967037 prefixEnd_2967037 := by exact prefixLift 2967037
  have htrace : WordTrace (prefixWord ++ tailWord_2967037) baseStart_2967037 baseEnd_2967037 := by
    simpa [prefixWord, tailWord_2967037, baseEnd_2967037] using wordTrace_append hprefix tailTrace_2967037
  have hstable : (prefixWord ++ tailWord_2967037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967037).length < 2 ^ (prefixWord ++ tailWord_2967037).sum := by decide
  have hdescent : baseEnd_2967037 < baseStart_2967037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967041 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2967041 : Nat := 118140960795 + 2967041 * 2 ^ 59
def prefixEnd_2967041 : Nat := 4983230072969 + 3 ^ 40 * 2967041 * 2
def baseEnd_2967041 : Nat := 507839384865610390714111

theorem tailTrace_2967041 : CollatzResearch.WordTrace tailWord_2967041 prefixEnd_2967041 507839384865610390714111 := by
  unfold tailWord_2967041
  simp only [CollatzResearch.WordTrace]
  refine ⟨108216875643924662105052977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72144583762616441403368651 108216875643924662105052977)
  ·
    refine ⟨81162656732943496578789733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108216875643924662105052977 81162656732943496578789733)
    ·
      refine ⟨15217998137426905608523075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81162656732943496578789733 15217998137426905608523075)
      ·
        refine ⟨22826997206140358412784613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15217998137426905608523075 22826997206140358412784613)
        ·
          refine ⟨4280061976151317202397115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22826997206140358412784613 4280061976151317202397115)
          ·
            refine ⟨6420092964226975803595673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280061976151317202397115 6420092964226975803595673)
            ·
              refine ⟨4815069723170231852696755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420092964226975803595673 4815069723170231852696755)
              ·
                refine ⟨7222604584755347779045133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815069723170231852696755 7222604584755347779045133)
                ·
                  refine ⟨2708476719283255417141925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7222604584755347779045133 2708476719283255417141925)
                  ·
                    refine ⟨507839384865610390714111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708476719283255417141925 507839384865610390714111)
                    ·
                      rfl

theorem cell23_2967041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2967041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967041 prefixEnd_2967041 := by exact prefixLift 2967041
  have htrace : WordTrace (prefixWord ++ tailWord_2967041) baseStart_2967041 baseEnd_2967041 := by
    simpa [prefixWord, tailWord_2967041, baseEnd_2967041] using wordTrace_append hprefix tailTrace_2967041
  have hstable : (prefixWord ++ tailWord_2967041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967041).length < 2 ^ (prefixWord ++ tailWord_2967041).sum := by decide
  have hdescent : baseEnd_2967041 < baseStart_2967041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967075 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 1, 4]
def baseStart_2967075 : Nat := 118140960795 + 2967075 * 2 ^ 59
def prefixEnd_2967075 : Nat := 4983230072969 + 3 ^ 40 * 2967075 * 2
def baseEnd_2967075 : Nat := 507845204313028013039059

theorem tailTrace_2967075 : CollatzResearch.WordTrace tailWord_2967075 prefixEnd_2967075 507845204313028013039059 := by
  unfold tailWord_2967075
  simp only [CollatzResearch.WordTrace]
  refine ⟨108218115725801485911790679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72145410483867657274527119 108218115725801485911790679)
  ·
    refine ⟨162327173588702228867686019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108218115725801485911790679 162327173588702228867686019)
    ·
      refine ⟨243490760383053343301529029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162327173588702228867686019 243490760383053343301529029)
      ·
        refine ⟨45654517571822501869036693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243490760383053343301529029 45654517571822501869036693)
        ·
          refine ⟨2140055511179179775111095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45654517571822501869036693 2140055511179179775111095)
          ·
            refine ⟨3210083266768769662666643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140055511179179775111095 3210083266768769662666643)
            ·
              refine ⟨4815124900153154493999965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210083266768769662666643 4815124900153154493999965)
              ·
                refine ⟨1805671837557432935249987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4815124900153154493999965 1805671837557432935249987)
                ·
                  refine ⟨2708507756336149402874981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805671837557432935249987 2708507756336149402874981)
                  ·
                    refine ⟨507845204313028013039059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708507756336149402874981 507845204313028013039059)
                    ·
                      rfl

theorem cell23_2967075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 4].length) (baseStart_2967075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967075 prefixEnd_2967075 := by exact prefixLift 2967075
  have htrace : WordTrace (prefixWord ++ tailWord_2967075) baseStart_2967075 baseEnd_2967075 := by
    simpa [prefixWord, tailWord_2967075, baseEnd_2967075] using wordTrace_append hprefix tailTrace_2967075
  have hstable : (prefixWord ++ tailWord_2967075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967075).length < 2 ^ (prefixWord ++ tailWord_2967075).sum := by decide
  have hdescent : baseEnd_2967075 < baseStart_2967075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967091 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 2, 3, 2]
def baseStart_2967091 : Nat := 118140960795 + 2967091 * 2 ^ 59
def prefixEnd_2967091 : Nat := 4983230072969 + 3 ^ 40 * 2967091 * 2
def baseEnd_2967091 : Nat := 1523543828629555976517103

theorem tailTrace_2967091 : CollatzResearch.WordTrace tailWord_2967091 prefixEnd_2967091 1523543828629555976517103 := by
  unfold tailWord_2967091
  simp only [CollatzResearch.WordTrace]
  refine ⟨108218699293743520644373127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72145799529162347096248751 108218699293743520644373127)
  ·
    refine ⟨162328048940615280966559691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108218699293743520644373127 162328048940615280966559691)
    ·
      refine ⟨243492073410922921449839537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162328048940615280966559691 243492073410922921449839537)
      ·
        refine ⟨182619055058192191087379653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243492073410922921449839537 182619055058192191087379653)
        ·
          refine ⟨34241072823411035828883685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182619055058192191087379653 34241072823411035828883685)
          ·
            refine ⟨6420201154389569217915691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34241072823411035828883685 6420201154389569217915691)
            ·
              refine ⟨9630301731584353826873537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6420201154389569217915691 9630301731584353826873537)
              ·
                refine ⟨7222726298688265370155153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9630301731584353826873537 7222726298688265370155153)
                ·
                  refine ⟨5417044724016199027616365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7222726298688265370155153 5417044724016199027616365)
                  ·
                    refine ⟨2031391771506074635356137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5417044724016199027616365 2031391771506074635356137)
                    ·
                      refine ⟨1523543828629555976517103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031391771506074635356137 1523543828629555976517103)
                      ·
                        rfl

theorem cell23_2967091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3, 2].length) (baseStart_2967091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967091 prefixEnd_2967091 := by exact prefixLift 2967091
  have htrace : WordTrace (prefixWord ++ tailWord_2967091) baseStart_2967091 baseEnd_2967091 := by
    simpa [prefixWord, tailWord_2967091, baseEnd_2967091] using wordTrace_append hprefix tailTrace_2967091
  have hstable : (prefixWord ++ tailWord_2967091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967091).length < 2 ^ (prefixWord ++ tailWord_2967091).sum := by decide
  have hdescent : baseEnd_2967091 < baseStart_2967091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967107 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 3]
def baseStart_2967107 : Nat := 118140960795 + 2967107 * 2 ^ 59
def prefixEnd_2967107 : Nat := 4983230072969 + 3 ^ 40 * 2967107 * 2
def baseEnd_2967107 : Nat := 1523552044320027913917029

theorem tailTrace_2967107 : CollatzResearch.WordTrace tailWord_2967107 prefixEnd_2967107 1523552044320027913917029 := by
  unfold tailWord_2967107
  simp only [CollatzResearch.WordTrace]
  refine ⟨108219282861685555376955575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72146188574457036917970383 108219282861685555376955575)
  ·
    refine ⟨162328924292528333065433363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108219282861685555376955575 162328924292528333065433363)
    ·
      refine ⟨243493386438792499598150045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162328924292528333065433363 243493386438792499598150045)
      ·
        refine ⟨91310019914547187349306267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243493386438792499598150045 91310019914547187349306267)
        ·
          refine ⟨136965029871820781023959401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91310019914547187349306267 136965029871820781023959401)
          ·
            refine ⟨102723772403865585767969551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136965029871820781023959401 102723772403865585767969551)
            ·
              refine ⟨154085658605798378651954327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102723772403865585767969551 154085658605798378651954327)
              ·
                refine ⟨231128487908697567977931491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154085658605798378651954327 231128487908697567977931491)
                ·
                  refine ⟨346692731863046351966897237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231128487908697567977931491 346692731863046351966897237)
                  ·
                    refine ⟨4062805451520074437112077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 346692731863046351966897237 4062805451520074437112077)
                    ·
                      refine ⟨1523552044320027913917029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062805451520074437112077 1523552044320027913917029)
                      ·
                        rfl

theorem cell23_2967107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_2967107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967107 prefixEnd_2967107 := by exact prefixLift 2967107
  have htrace : WordTrace (prefixWord ++ tailWord_2967107) baseStart_2967107 baseEnd_2967107 := by
    simpa [prefixWord, tailWord_2967107, baseEnd_2967107] using wordTrace_append hprefix tailTrace_2967107
  have hstable : (prefixWord ++ tailWord_2967107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967107).length < 2 ^ (prefixWord ++ tailWord_2967107).sum := by decide
  have hdescent : baseEnd_2967107 < baseStart_2967107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967121 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 5, 2, 2]
def baseStart_2967121 : Nat := 118140960795 + 2967121 * 2 ^ 59
def prefixEnd_2967121 : Nat := 4983230072969 + 3 ^ 40 * 2967121 * 2
def baseEnd_2967121 : Nat := 1523559233049190859141965

theorem tailTrace_2967121 : CollatzResearch.WordTrace tailWord_2967121 prefixEnd_2967121 1523559233049190859141965 := by
  unfold tailWord_2967121
  simp only [CollatzResearch.WordTrace]
  refine ⟨108219793483634835767965217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72146528989089890511976811 108219793483634835767965217)
  ·
    refine ⟨81164845112726126825973913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108219793483634835767965217 81164845112726126825973913)
    ·
      refine ⟨60873633834544595119480435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81164845112726126825973913 60873633834544595119480435)
      ·
        refine ⟨91310450751816892679220653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60873633834544595119480435 91310450751816892679220653)
        ·
          refine ⟨34241419031931334754707745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91310450751816892679220653 34241419031931334754707745)
          ·
            refine ⟨25681064273948501066030809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34241419031931334754707745 25681064273948501066030809)
            ·
              refine ⟨19260798205461375799523107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25681064273948501066030809 19260798205461375799523107)
              ·
                refine ⟨28891197308192063699284661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19260798205461375799523107 28891197308192063699284661)
                ·
                  refine ⟨2708549747643005971807937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28891197308192063699284661 2708549747643005971807937)
                  ·
                    refine ⟨2031412310732254478855953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2708549747643005971807937 2031412310732254478855953)
                    ·
                      refine ⟨1523559233049190859141965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031412310732254478855953 1523559233049190859141965)
                      ·
                        rfl

theorem cell23_2967121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_2967121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967121 prefixEnd_2967121 := by exact prefixLift 2967121
  have htrace : WordTrace (prefixWord ++ tailWord_2967121) baseStart_2967121 baseEnd_2967121 := by
    simpa [prefixWord, tailWord_2967121, baseEnd_2967121] using wordTrace_append hprefix tailTrace_2967121
  have hstable : (prefixWord ++ tailWord_2967121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967121).length < 2 ^ (prefixWord ++ tailWord_2967121).sum := by decide
  have hdescent : baseEnd_2967121 < baseStart_2967121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967127 : List Nat := [1, 1, 3, 2, 2, 3, 2, 9]
def baseStart_2967127 : Nat := 118140960795 + 2967127 * 2 ^ 59
def prefixEnd_2967127 : Nat := 4983230072969 + 3 ^ 40 * 2967127 * 2
def baseEnd_2967127 : Nat := 56428233849374734654331

theorem tailTrace_2967127 : CollatzResearch.WordTrace tailWord_2967127 prefixEnd_2967127 56428233849374734654331 := by
  unfold tailWord_2967127
  simp only [CollatzResearch.WordTrace]
  refine ⟨108220012321613098792683635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72146674881075399195122423 108220012321613098792683635)
  ·
    refine ⟨162330018482419648189025453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108220012321613098792683635 162330018482419648189025453)
    ·
      refine ⟨60873756930907368070884545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162330018482419648189025453 60873756930907368070884545)
      ·
        refine ⟨45655317698180526053163409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60873756930907368070884545 45655317698180526053163409)
        ·
          refine ⟨34241488273635394539872557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45655317698180526053163409 34241488273635394539872557)
          ·
            refine ⟨12840558102613272952452209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34241488273635394539872557 12840558102613272952452209)
            ·
              refine ⟨9630418576959954714339157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12840558102613272952452209 9630418576959954714339157)
              ·
                refine ⟨56428233849374734654331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9630418576959954714339157 56428233849374734654331)
                ·
                  rfl

theorem cell23_2967127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 9].length) (baseStart_2967127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967127 prefixEnd_2967127 := by exact prefixLift 2967127
  have htrace : WordTrace (prefixWord ++ tailWord_2967127) baseStart_2967127 baseEnd_2967127 := by
    simpa [prefixWord, tailWord_2967127, baseEnd_2967127] using wordTrace_append hprefix tailTrace_2967127
  have hstable : (prefixWord ++ tailWord_2967127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967127).length < 2 ^ (prefixWord ++ tailWord_2967127).sum := by decide
  have hdescent : baseEnd_2967127 < baseStart_2967127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967141 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2967141 : Nat := 118140960795 + 2967141 * 2 ^ 59
def prefixEnd_2967141 : Nat := 4983230072969 + 3 ^ 40 * 2967141 * 2
def baseEnd_2967141 : Nat := 1523569502662280780891873

theorem tailTrace_2967141 : CollatzResearch.WordTrace tailWord_2967141 prefixEnd_2967141 1523569502662280780891873 := by
  unfold tailWord_2967141
  simp only [CollatzResearch.WordTrace]
  refine ⟨108220522943562379183693277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72147015295708252789128851 108220522943562379183693277)
  ·
    refine ⟨40582696103835892193884979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108220522943562379183693277 40582696103835892193884979)
    ·
      refine ⟨60874044155753838290827469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40582696103835892193884979 60874044155753838290827469)
      ·
        refine ⟨22827766558407689359060301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60874044155753838290827469 22827766558407689359060301)
        ·
          refine ⟨8560412459402883509647613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22827766558407689359060301 8560412459402883509647613)
          ·
            refine ⟨3210154672276081316117855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8560412459402883509647613 3210154672276081316117855)
            ·
              refine ⟨4815232008414121974176783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210154672276081316117855 4815232008414121974176783)
              ·
                refine ⟨7222848012621182961265175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815232008414121974176783 7222848012621182961265175)
                ·
                  refine ⟨10834272018931774441897763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7222848012621182961265175 10834272018931774441897763)
                  ·
                    refine ⟨16251408028397661662846645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10834272018931774441897763 16251408028397661662846645)
                    ·
                      refine ⟨1523569502662280780891873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16251408028397661662846645 1523569502662280780891873)
                      ·
                        rfl

theorem cell23_2967141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2967141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967141 prefixEnd_2967141 := by exact prefixLift 2967141
  have htrace : WordTrace (prefixWord ++ tailWord_2967141) baseStart_2967141 baseEnd_2967141 := by
    simpa [prefixWord, tailWord_2967141, baseEnd_2967141] using wordTrace_append hprefix tailTrace_2967141
  have hstable : (prefixWord ++ tailWord_2967141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967141).length < 2 ^ (prefixWord ++ tailWord_2967141).sum := by decide
  have hdescent : baseEnd_2967141 < baseStart_2967141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967149 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_2967149 : Nat := 118140960795 + 2967149 * 2 ^ 59
def prefixEnd_2967149 : Nat := 4983230072969 + 3 ^ 40 * 2967149 * 2
def baseEnd_2967149 : Nat := 1523573610507516749591837

theorem tailTrace_2967149 : CollatzResearch.WordTrace tailWord_2967149 prefixEnd_2967149 1523573610507516749591837 := by
  unfold tailWord_2967149
  simp only [CollatzResearch.WordTrace]
  refine ⟨108220814727533396549984501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72147209818355597699989667 108220814727533396549984501)
  ·
    refine ⟨10145701380706255926561047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108220814727533396549984501 10145701380706255926561047)
    ·
      refine ⟨15218552071059383889841571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10145701380706255926561047 15218552071059383889841571)
      ·
        refine ⟨22827828106589075834762357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15218552071059383889841571 22827828106589075834762357)
        ·
          refine ⟨2140108884992725859508971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22827828106589075834762357 2140108884992725859508971)
          ·
            refine ⟨3210163327489088789263457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140108884992725859508971 3210163327489088789263457)
            ·
              refine ⟨2407622495616816591947593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210163327489088789263457 2407622495616816591947593)
              ·
                refine ⟨1805716871712612443960695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407622495616816591947593 1805716871712612443960695)
                ·
                  refine ⟨2708575307568918665941043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805716871712612443960695 2708575307568918665941043)
                  ·
                    refine ⟨4062862961353377998911565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708575307568918665941043 4062862961353377998911565)
                    ·
                      refine ⟨1523573610507516749591837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4062862961353377998911565 1523573610507516749591837)
                      ·
                        rfl

theorem cell23_2967149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_2967149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967149 prefixEnd_2967149 := by exact prefixLift 2967149
  have htrace : WordTrace (prefixWord ++ tailWord_2967149) baseStart_2967149 baseEnd_2967149 := by
    simpa [prefixWord, tailWord_2967149, baseEnd_2967149] using wordTrace_append hprefix tailTrace_2967149
  have hstable : (prefixWord ++ tailWord_2967149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967149).length < 2 ^ (prefixWord ++ tailWord_2967149).sum := by decide
  have hdescent : baseEnd_2967149 < baseStart_2967149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967187 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 6, 6]
def baseStart_2967187 : Nat := 118140960795 + 2967187 * 2 ^ 59
def prefixEnd_2967187 : Nat := 4983230072969 + 3 ^ 40 * 2967187 * 2
def baseEnd_2967187 : Nat := 507864374257462533638887

theorem tailTrace_2967187 : CollatzResearch.WordTrace tailWord_2967187 prefixEnd_2967187 507864374257462533638887 := by
  unfold tailWord_2967187
  simp only [CollatzResearch.WordTrace]
  refine ⟨108222200701395729039867815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72148133800930486026578543 108222200701395729039867815)
  ·
    refine ⟨162333301052093593559801723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108222200701395729039867815 162333301052093593559801723)
    ·
      refine ⟨243499951578140390339702585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162333301052093593559801723 243499951578140390339702585)
      ·
        refine ⟨182624963683605292754776939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243499951578140390339702585 182624963683605292754776939)
        ·
          refine ⟨273937445525407939132165409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182624963683605292754776939 273937445525407939132165409)
          ·
            refine ⟨205453084144055954349124057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273937445525407939132165409 205453084144055954349124057)
            ·
              refine ⟨154089813108041965761843043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205453084144055954349124057 154089813108041965761843043)
              ·
                refine ⟨231134719662062948642764565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154089813108041965761843043 231134719662062948642764565)
                ·
                  refine ⟨10834439984159200717629589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231134719662062948642764565 10834439984159200717629589)
                  ·
                    refine ⟨507864374257462533638887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10834439984159200717629589 507864374257462533638887)
                    ·
                      rfl

theorem cell23_2967187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 6].length) (baseStart_2967187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967187 prefixEnd_2967187 := by exact prefixLift 2967187
  have htrace : WordTrace (prefixWord ++ tailWord_2967187) baseStart_2967187 baseEnd_2967187 := by
    simpa [prefixWord, tailWord_2967187, baseEnd_2967187] using wordTrace_append hprefix tailTrace_2967187
  have hstable : (prefixWord ++ tailWord_2967187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967187).length < 2 ^ (prefixWord ++ tailWord_2967187).sum := by decide
  have hdescent : baseEnd_2967187 < baseStart_2967187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967204 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_2967204 : Nat := 118140960795 + 2967204 * 2 ^ 59
def prefixEnd_2967204 : Nat := 4983230072969 + 3 ^ 40 * 2967204 * 2
def baseEnd_2967204 : Nat := 507867283981171344801361

theorem tailTrace_2967204 : CollatzResearch.WordTrace tailWord_2967204 prefixEnd_2967204 507867283981171344801361 := by
  unfold tailWord_2967204
  simp only [CollatzResearch.WordTrace]
  refine ⟨54111410371167070471618333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72148547161556093962157777 54111410371167070471618333)
  ·
    refine ⟨20291778889187651426856875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54111410371167070471618333 20291778889187651426856875)
    ·
      refine ⟨30437668333781477140285313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20291778889187651426856875 30437668333781477140285313)
      ·
        refine ⟨22828251250336107855213985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30437668333781477140285313 22828251250336107855213985)
        ·
          refine ⟨17121188437752080891410489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22828251250336107855213985 17121188437752080891410489)
          ·
            refine ⟨12840891328314060668557867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17121188437752080891410489 12840891328314060668557867)
            ·
              refine ⟨19261336992471091002836801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12840891328314060668557867 19261336992471091002836801)
              ·
                refine ⟨14446002744353318252127601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19261336992471091002836801 14446002744353318252127601)
                ·
                  refine ⟨10834502058264988689095701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14446002744353318252127601 10834502058264988689095701)
                  ·
                    refine ⟨507867283981171344801361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10834502058264988689095701 507867283981171344801361)
                    ·
                      rfl

theorem cell23_2967204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_2967204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967204 prefixEnd_2967204 := by exact prefixLift 2967204
  have htrace : WordTrace (prefixWord ++ tailWord_2967204) baseStart_2967204 baseEnd_2967204 := by
    simpa [prefixWord, tailWord_2967204, baseEnd_2967204] using wordTrace_append hprefix tailTrace_2967204
  have hstable : (prefixWord ++ tailWord_2967204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967204).length < 2 ^ (prefixWord ++ tailWord_2967204).sum := by decide
  have hdescent : baseEnd_2967204 < baseStart_2967204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967227 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_2967227 : Nat := 118140960795 + 2967227 * 2 ^ 59
def prefixEnd_2967227 : Nat := 4983230072969 + 3 ^ 40 * 2967227 * 2
def baseEnd_2967227 : Nat := 1523613661998567444416477

theorem tailTrace_2967227 : CollatzResearch.WordTrace tailWord_2967227 prefixEnd_2967227 1523613661998567444416477 := by
  unfold tailWord_2967227
  simp only [CollatzResearch.WordTrace]
  refine ⟨108223659621250815871323935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72149106414167210580882623 108223659621250815871323935)
  ·
    refine ⟨162335489431876223806985903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108223659621250815871323935 162335489431876223806985903)
    ·
      refine ⟨243503234147814335710478855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162335489431876223806985903 243503234147814335710478855)
      ·
        refine ⟨365254851221721503565718283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243503234147814335710478855 365254851221721503565718283)
        ·
          refine ⟨547882276832582255348577425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365254851221721503565718283 547882276832582255348577425)
          ·
            refine ⟨410911707624436691511433069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547882276832582255348577425 410911707624436691511433069)
            ·
              refine ⟨154091890359163759316787401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410911707624436691511433069 154091890359163759316787401)
              ·
                refine ⟨115568917769372819487590551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154091890359163759316787401 115568917769372819487590551)
                ·
                  refine ⟨173353376654059229231385827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115568917769372819487590551 173353376654059229231385827)
                  ·
                    refine ⟨260030064981088843847078741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173353376654059229231385827 260030064981088843847078741)
                    ·
                      refine ⟨1523613661998567444416477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 260030064981088843847078741 1523613661998567444416477)
                      ·
                        rfl

theorem cell23_2967227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_2967227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967227 prefixEnd_2967227 := by exact prefixLift 2967227
  have htrace : WordTrace (prefixWord ++ tailWord_2967227) baseStart_2967227 baseEnd_2967227 := by
    simpa [prefixWord, tailWord_2967227, baseEnd_2967227] using wordTrace_append hprefix tailTrace_2967227
  have hstable : (prefixWord ++ tailWord_2967227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967227).length < 2 ^ (prefixWord ++ tailWord_2967227).sum := by decide
  have hdescent : baseEnd_2967227 < baseStart_2967227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967228 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2967228 : Nat := 118140960795 + 2967228 * 2 ^ 59
def prefixEnd_2967228 : Nat := 4983230072969 + 3 ^ 40 * 2967228 * 2
def baseEnd_2967228 : Nat := 1523614175479221940503973

theorem tailTrace_2967228 : CollatzResearch.WordTrace tailWord_2967228 prefixEnd_2967228 1523614175479221940503973 := by
  unfold tailWord_2967228
  simp only [CollatzResearch.WordTrace]
  refine ⟨54111848047123596521055169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72149130729498128694740225 54111848047123596521055169)
  ·
    refine ⟨40583886035342697390791377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54111848047123596521055169 40583886035342697390791377)
    ·
      refine ⟨30437914526507023043093533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40583886035342697390791377 30437914526507023043093533)
      ·
        refine ⟨11414217947440133641160075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30437914526507023043093533 11414217947440133641160075)
        ·
          refine ⟨17121326921160200461740113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11414217947440133641160075 17121326921160200461740113)
          ·
            refine ⟨12840995190870150346305085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17121326921160200461740113 12840995190870150346305085)
            ·
              refine ⟨4815373196576306379864407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12840995190870150346305085 4815373196576306379864407)
              ·
                refine ⟨7223059794864459569796611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815373196576306379864407 7223059794864459569796611)
                ·
                  refine ⟨10834589692296689354694917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7223059794864459569796611 10834589692296689354694917)
                  ·
                    refine ⟨2031485567305629254005297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10834589692296689354694917 2031485567305629254005297)
                    ·
                      refine ⟨1523614175479221940503973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031485567305629254005297 1523614175479221940503973)
                      ·
                        rfl

theorem cell23_2967228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2967228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967228 prefixEnd_2967228 := by exact prefixLift 2967228
  have htrace : WordTrace (prefixWord ++ tailWord_2967228) baseStart_2967228 baseEnd_2967228 := by
    simpa [prefixWord, tailWord_2967228, baseEnd_2967228] using wordTrace_append hprefix tailTrace_2967228
  have hstable : (prefixWord ++ tailWord_2967228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967228).length < 2 ^ (prefixWord ++ tailWord_2967228).sum := by decide
  have hdescent : baseEnd_2967228 < baseStart_2967228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967264 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_2967264 : Nat := 118140960795 + 2967264 * 2 ^ 59
def prefixEnd_2967264 : Nat := 4983230072969 + 3 ^ 40 * 2967264 * 2
def baseEnd_2967264 : Nat := 507877553594261266551269

theorem tailTrace_2967264 : CollatzResearch.WordTrace tailWord_2967264 prefixEnd_2967264 507877553594261266551269 := by
  unfold tailWord_2967264
  simp only [CollatzResearch.WordTrace]
  refine ⟨54112504561058385595210423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72150006081411180793613897 54112504561058385595210423)
  ·
    refine ⟨81168756841587578392815635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54112504561058385595210423 81168756841587578392815635)
    ·
      refine ⟨121753135262381367589223453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81168756841587578392815635 121753135262381367589223453)
      ·
        refine ⟨45657425723393012845958795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121753135262381367589223453 45657425723393012845958795)
        ·
          refine ⟨68486138585089519268938193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45657425723393012845958795 68486138585089519268938193)
          ·
            refine ⟨51364603938817139451703645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68486138585089519268938193 51364603938817139451703645)
            ·
              refine ⟨19261726477056427294388867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51364603938817139451703645 19261726477056427294388867)
              ·
                refine ⟨28892589715584640941583301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19261726477056427294388867 28892589715584640941583301)
                ·
                  refine ⟨5417360571672120176546869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28892589715584640941583301 5417360571672120176546869)
                  ·
                    refine ⟨507877553594261266551269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5417360571672120176546869 507877553594261266551269)
                    ·
                      rfl

theorem cell23_2967264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_2967264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967264 prefixEnd_2967264 := by exact prefixLift 2967264
  have htrace : WordTrace (prefixWord ++ tailWord_2967264) baseStart_2967264 baseEnd_2967264 := by
    simpa [prefixWord, tailWord_2967264, baseEnd_2967264] using wordTrace_append hprefix tailTrace_2967264
  have hstable : (prefixWord ++ tailWord_2967264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967264).length < 2 ^ (prefixWord ++ tailWord_2967264).sum := by decide
  have hdescent : baseEnd_2967264 < baseStart_2967264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967268 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 5]
def baseStart_2967268 : Nat := 118140960795 + 2967268 * 2 ^ 59
def prefixEnd_2967268 : Nat := 4983230072969 + 3 ^ 40 * 2967268 * 2
def baseEnd_2967268 : Nat := 169292746078377976000421

theorem tailTrace_2967268 : CollatzResearch.WordTrace tailWord_2967268 prefixEnd_2967268 169292746078377976000421 := by
  unfold tailWord_2967268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54112577507051139936783229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72150103342734853249044305 54112577507051139936783229)
  ·
    refine ⟨20292216565144177476293711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54112577507051139936783229 20292216565144177476293711)
    ·
      refine ⟨30438324847716266214440567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20292216565144177476293711 30438324847716266214440567)
      ·
        refine ⟨45657487271574399321660851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30438324847716266214440567 45657487271574399321660851)
        ·
          refine ⟨68486230907361598982491277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45657487271574399321660851 68486230907361598982491277)
          ·
            refine ⟨25682336590260599618434229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68486230907361598982491277 25682336590260599618434229)
            ·
              refine ⟨2407719055336931214228209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25682336590260599618434229 2407719055336931214228209)
              ·
                refine ⟨1805789291502698410671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407719055336931214228209 1805789291502698410671157)
                ·
                  refine ⟨169292746078377976000421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805789291502698410671157 169292746078377976000421)
                  ·
                    rfl

theorem cell23_2967268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_2967268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967268 prefixEnd_2967268 := by exact prefixLift 2967268
  have htrace : WordTrace (prefixWord ++ tailWord_2967268) baseStart_2967268 baseEnd_2967268 := by
    simpa [prefixWord, tailWord_2967268, baseEnd_2967268] using wordTrace_append hprefix tailTrace_2967268
  have hstable : (prefixWord ++ tailWord_2967268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967268).length < 2 ^ (prefixWord ++ tailWord_2967268).sum := by decide
  have hdescent : baseEnd_2967268 < baseStart_2967268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967274 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2967274 : Nat := 118140960795 + 2967274 * 2 ^ 59
def prefixEnd_2967274 : Nat := 4983230072969 + 3 ^ 40 * 2967274 * 2
def baseEnd_2967274 : Nat := 1523637795589328760528761

theorem tailTrace_2967274 : CollatzResearch.WordTrace tailWord_2967274 prefixEnd_2967274 1523637795589328760528761 := by
  unfold tailWord_2967274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27056343463020135724571219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72150249234720361932189917 27056343463020135724571219)
  ·
    refine ⟨40584515194530203586856829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27056343463020135724571219 40584515194530203586856829)
    ·
      refine ⟨15219193197948826345071311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40584515194530203586856829 15219193197948826345071311)
      ·
        refine ⟨22828789796923239517606967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15219193197948826345071311 22828789796923239517606967)
        ·
          refine ⟨34243184695384859276410451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22828789796923239517606967 34243184695384859276410451)
          ·
            refine ⟨51364777043077288914615677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34243184695384859276410451 51364777043077288914615677)
            ·
              refine ⟨19261791391153983342980879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51364777043077288914615677 19261791391153983342980879)
              ·
                refine ⟨28892687086730975014471319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19261791391153983342980879 28892687086730975014471319)
                ·
                  refine ⟨43339030630096462521706979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28892687086730975014471319 43339030630096462521706979)
                  ·
                    refine ⟨65008545945144693782560469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43339030630096462521706979 65008545945144693782560469)
                    ·
                      refine ⟨1523637795589328760528761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65008545945144693782560469 1523637795589328760528761)
                      ·
                        rfl

theorem cell23_2967274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2967274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967274 prefixEnd_2967274 := by exact prefixLift 2967274
  have htrace : WordTrace (prefixWord ++ tailWord_2967274) baseStart_2967274 baseEnd_2967274 := by
    simpa [prefixWord, tailWord_2967274, baseEnd_2967274] using wordTrace_append hprefix tailTrace_2967274
  have hstable : (prefixWord ++ tailWord_2967274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967274).length < 2 ^ (prefixWord ++ tailWord_2967274).sum := by decide
  have hdescent : baseEnd_2967274 < baseStart_2967274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967298 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2967298 : Nat := 118140960795 + 2967298 * 2 ^ 59
def prefixEnd_2967298 : Nat := 4983230072969 + 3 ^ 40 * 2967298 * 2
def baseEnd_2967298 : Nat := 507883373041678888876217

theorem tailTrace_2967298 : CollatzResearch.WordTrace tailWord_2967298 prefixEnd_2967298 507883373041678888876217 := by
  unfold tailWord_2967298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27056562300998398749289637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72150832802662396664772365 27056562300998398749289637)
  ·
    refine ⟨5073105431437199765491807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27056562300998398749289637 5073105431437199765491807)
    ·
      refine ⟨7609658147155799648237711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073105431437199765491807 7609658147155799648237711)
      ·
        refine ⟨11414487220733699472356567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609658147155799648237711 11414487220733699472356567)
        ·
          refine ⟨17121730831100549208534851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11414487220733699472356567 17121730831100549208534851)
          ·
            refine ⟨25682596246650823812802277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17121730831100549208534851 25682596246650823812802277)
            ·
              refine ⟨4815486796247029464900427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25682596246650823812802277 4815486796247029464900427)
              ·
                refine ⟨7223230194370544197350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815486796247029464900427 7223230194370544197350641)
                ·
                  refine ⟨5417422645777908148012981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7223230194370544197350641 5417422645777908148012981)
                  ·
                    refine ⟨507883373041678888876217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5417422645777908148012981 507883373041678888876217)
                    ·
                      rfl

theorem cell23_2967298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2967298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967298 prefixEnd_2967298 := by exact prefixLift 2967298
  have htrace : WordTrace (prefixWord ++ tailWord_2967298) baseStart_2967298 baseEnd_2967298 := by
    simpa [prefixWord, tailWord_2967298, baseEnd_2967298] using wordTrace_append hprefix tailTrace_2967298
  have hstable : (prefixWord ++ tailWord_2967298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967298).length < 2 ^ (prefixWord ++ tailWord_2967298).sum := by decide
  have hdescent : baseEnd_2967298 < baseStart_2967298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967301 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 6, 4, 2]
def baseStart_2967301 : Nat := 118140960795 + 2967301 * 2 ^ 59
def prefixEnd_2967301 : Nat := 4983230072969 + 3 ^ 40 * 2967301 * 2
def baseEnd_2967301 : Nat := 1523651659567000154891137

theorem tailTrace_2967301 : CollatzResearch.WordTrace tailWord_2967301 prefixEnd_2967301 1523651659567000154891137 := by
  unfold tailWord_2967301
  simp only [CollatzResearch.WordTrace]
  refine ⟨108226358622982726509517757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72150905748655151006345171 108226358622982726509517757)
  ·
    refine ⟨40584884483618522441069159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108226358622982726509517757 40584884483618522441069159)
    ·
      refine ⟨60877326725427783661603739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40584884483618522441069159 60877326725427783661603739)
      ·
        refine ⟨91315990088141675492405609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60877326725427783661603739 91315990088141675492405609)
        ·
          refine ⟨68486992566106256619304207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91315990088141675492405609 68486992566106256619304207)
          ·
            refine ⟨102730488849159384928956311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68486992566106256619304207 102730488849159384928956311)
            ·
              refine ⟨154095733273739077393434467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102730488849159384928956311 154095733273739077393434467)
              ·
                refine ⟨231143599910608616090151701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154095733273739077393434467 231143599910608616090151701)
                ·
                  refine ⟨10834856245809778879225861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231143599910608616090151701 10834856245809778879225861)
                  ·
                    refine ⟨2031535546089333539854849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10834856245809778879225861 2031535546089333539854849)
                    ·
                      refine ⟨1523651659567000154891137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031535546089333539854849 1523651659567000154891137)
                      ·
                        rfl

theorem cell23_2967301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_2967301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967301 prefixEnd_2967301 := by exact prefixLift 2967301
  have htrace : WordTrace (prefixWord ++ tailWord_2967301) baseStart_2967301 baseEnd_2967301 := by
    simpa [prefixWord, tailWord_2967301, baseEnd_2967301] using wordTrace_append hprefix tailTrace_2967301
  have hstable : (prefixWord ++ tailWord_2967301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967301).length < 2 ^ (prefixWord ++ tailWord_2967301).sum := by decide
  have hdescent : baseEnd_2967301 < baseStart_2967301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967384 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_2967384 : Nat := 118140960795 + 2967384 * 2 ^ 59
def prefixEnd_2967384 : Nat := 4983230072969 + 3 ^ 40 * 2967384 * 2
def baseEnd_2967384 : Nat := 507898092820441110051085

theorem tailTrace_2967384 : CollatzResearch.WordTrace tailWord_2967384 prefixEnd_2967384 507898092820441110051085 := by
  unfold tailWord_2967384
  simp only [CollatzResearch.WordTrace]
  refine ⟨54114692940841015842394603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72152923921121354456526137 54114692940841015842394603)
  ·
    refine ⟨81172039411261523763591905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54114692940841015842394603 81172039411261523763591905)
    ·
      refine ⟨60879029558446142822693929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81172039411261523763591905 60879029558446142822693929)
      ·
        refine ⟨45659272168834607117020447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60879029558446142822693929 45659272168834607117020447)
        ·
          refine ⟨68488908253251910675530671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45659272168834607117020447 68488908253251910675530671)
          ·
            refine ⟨102733362379877866013296007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68488908253251910675530671 102733362379877866013296007)
            ·
              refine ⟨154100043569816799019944011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102733362379877866013296007 154100043569816799019944011)
              ·
                refine ⟨231150065354725198529916017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154100043569816799019944011 231150065354725198529916017)
                ·
                  refine ⟨173362549016043898897437013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231150065354725198529916017 173362549016043898897437013)
                  ·
                    refine ⟨507898092820441110051085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 173362549016043898897437013 507898092820441110051085)
                    ·
                      rfl

theorem cell23_2967384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_2967384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967384 prefixEnd_2967384 := by exact prefixLift 2967384
  have htrace : WordTrace (prefixWord ++ tailWord_2967384) baseStart_2967384 baseEnd_2967384 := by
    simpa [prefixWord, tailWord_2967384, baseEnd_2967384] using wordTrace_append hprefix tailTrace_2967384
  have hstable : (prefixWord ++ tailWord_2967384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967384).length < 2 ^ (prefixWord ++ tailWord_2967384).sum := by decide
  have hdescent : baseEnd_2967384 < baseStart_2967384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967385 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 1, 1, 3]
def baseStart_2967385 : Nat := 118140960795 + 2967385 * 2 ^ 59
def prefixEnd_2967385 : Nat := 4983230072969 + 3 ^ 40 * 2967385 * 2
def baseEnd_2967385 : Nat := 1523694791941977826240751

theorem tailTrace_2967385 : CollatzResearch.WordTrace tailWord_2967385 prefixEnd_2967385 1523694791941977826240751 := by
  unfold tailWord_2967385
  simp only [CollatzResearch.WordTrace]
  refine ⟨108229422354678408855575609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72152948236452272570383739 108229422354678408855575609)
  ·
    refine ⟨81172066766008806641681707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108229422354678408855575609 81172066766008806641681707)
    ·
      refine ⟨121758100149013209962522561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81172066766008806641681707 121758100149013209962522561)
      ·
        refine ⟨91318575111759907471891921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121758100149013209962522561 91318575111759907471891921)
        ·
          refine ⟨68488931333819930603918941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91318575111759907471891921 68488931333819930603918941)
          ·
            refine ⟨25683349250182473976469603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68488931333819930603918941 25683349250182473976469603)
            ·
              refine ⟨38525023875273710964704405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25683349250182473976469603 38525023875273710964704405)
              ·
                refine ⟨1805860494153455201470519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38525023875273710964704405 1805860494153455201470519)
                ·
                  refine ⟨2708790741230182802205779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805860494153455201470519 2708790741230182802205779)
                  ·
                    refine ⟨4063186111845274203308669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708790741230182802205779 4063186111845274203308669)
                    ·
                      refine ⟨1523694791941977826240751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4063186111845274203308669 1523694791941977826240751)
                      ·
                        rfl

theorem cell23_2967385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_2967385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967385 prefixEnd_2967385 := by exact prefixLift 2967385
  have htrace : WordTrace (prefixWord ++ tailWord_2967385) baseStart_2967385 baseEnd_2967385 := by
    simpa [prefixWord, tailWord_2967385, baseEnd_2967385] using wordTrace_append hprefix tailTrace_2967385
  have hstable : (prefixWord ++ tailWord_2967385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967385).length < 2 ^ (prefixWord ++ tailWord_2967385).sum := by decide
  have hdescent : baseEnd_2967385 < baseStart_2967385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967421 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_2967421 : Nat := 118140960795 + 2967421 * 2 ^ 59
def prefixEnd_2967421 : Nat := 4983230072969 + 3 ^ 40 * 2967421 * 2
def baseEnd_2967421 : Nat := 1523713277245539685390585

theorem tailTrace_2967421 : CollatzResearch.WordTrace tailWord_2967421 prefixEnd_2967421 1523713277245539685390585 := by
  unfold tailWord_2967421
  simp only [CollatzResearch.WordTrace]
  refine ⟨108230735382547987003886117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72153823588365324669257411 108230735382547987003886117)
  ·
    refine ⟨20293262884227747563228647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108230735382547987003886117 20293262884227747563228647)
    ·
      refine ⟨30439894326341621344842971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20293262884227747563228647 30439894326341621344842971)
      ·
        refine ⟨45659841489512432017264457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30439894326341621344842971 45659841489512432017264457)
        ·
          refine ⟨34244881117134324012948343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45659841489512432017264457 34244881117134324012948343)
          ·
            refine ⟨51367321675701486019422515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34244881117134324012948343 51367321675701486019422515)
            ·
              refine ⟨77050982513552229029133773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51367321675701486019422515 77050982513552229029133773)
              ·
                refine ⟨28894118442582085885925165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77050982513552229029133773 28894118442582085885925165)
                ·
                  refine ⟨10835294415968282207221937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28894118442582085885925165 10835294415968282207221937)
                  ·
                    refine ⟨8126470811976211655416453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10835294415968282207221937 8126470811976211655416453)
                    ·
                      refine ⟨1523713277245539685390585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8126470811976211655416453 1523713277245539685390585)
                      ·
                        rfl

theorem cell23_2967421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_2967421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967421 prefixEnd_2967421 := by exact prefixLift 2967421
  have htrace : WordTrace (prefixWord ++ tailWord_2967421) baseStart_2967421 baseEnd_2967421 := by
    simpa [prefixWord, tailWord_2967421, baseEnd_2967421] using wordTrace_append hprefix tailTrace_2967421
  have hstable : (prefixWord ++ tailWord_2967421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967421).length < 2 ^ (prefixWord ++ tailWord_2967421).sum := by decide
  have hdescent : baseEnd_2967421 < baseStart_2967421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967452 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2967452 : Nat := 118140960795 + 2967452 * 2 ^ 59
def prefixEnd_2967452 : Nat := 4983230072969 + 3 ^ 40 * 2967452 * 2
def baseEnd_2967452 : Nat := 507909731715276354700981

theorem tailTrace_2967452 : CollatzResearch.WordTrace tailWord_2967452 prefixEnd_2967452 507909731715276354700981 := by
  unfold tailWord_2967452
  simp only [CollatzResearch.WordTrace]
  refine ⟨54115933022717839649132305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72154577363623786198843073 54115933022717839649132305)
  ·
    refine ⟨40586949767038379736849229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54115933022717839649132305 40586949767038379736849229)
    ·
      refine ⟨15220106162639392401318461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40586949767038379736849229 15220106162639392401318461)
      ·
        refine ⟨5707539810989772150494423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15220106162639392401318461 5707539810989772150494423)
        ·
          refine ⟨8561309716484658225741635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707539810989772150494423 8561309716484658225741635)
          ·
            refine ⟨12841964574726987338612453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8561309716484658225741635 12841964574726987338612453)
            ·
              refine ⟨2407868357761310125989835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12841964574726987338612453 2407868357761310125989835)
              ·
                refine ⟨3611802536641965188984753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407868357761310125989835 3611802536641965188984753)
                ·
                  refine ⟨2708851902481473891738565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3611802536641965188984753 2708851902481473891738565)
                  ·
                    refine ⟨507909731715276354700981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708851902481473891738565 507909731715276354700981)
                    ·
                      rfl

theorem cell23_2967452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2967452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967452 prefixEnd_2967452 := by exact prefixLift 2967452
  have htrace : WordTrace (prefixWord ++ tailWord_2967452) baseStart_2967452 baseEnd_2967452 := by
    simpa [prefixWord, tailWord_2967452, baseEnd_2967452] using wordTrace_append hprefix tailTrace_2967452
  have hstable : (prefixWord ++ tailWord_2967452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967452).length < 2 ^ (prefixWord ++ tailWord_2967452).sum := by decide
  have hdescent : baseEnd_2967452 < baseStart_2967452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967508 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_2967508 : Nat := 118140960795 + 2967508 * 2 ^ 59
def prefixEnd_2967508 : Nat := 4983230072969 + 3 ^ 40 * 2967508 * 2
def baseEnd_2967508 : Nat := 507919316687493615000895

theorem tailTrace_2967508 : CollatzResearch.WordTrace tailWord_2967508 prefixEnd_2967508 507919316687493615000895 := by
  unfold tailWord_2967508
  simp only [CollatzResearch.WordTrace]
  refine ⟨54116954266616400431151589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72155939022155200574868785 54116954266616400431151589)
  ·
    refine ⟨10146928924990575080840923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54116954266616400431151589 10146928924990575080840923)
    ·
      refine ⟨15220393387485862621261385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10146928924990575080840923 15220393387485862621261385)
      ·
        refine ⟨11415295040614396965946039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15220393387485862621261385 11415295040614396965946039)
        ·
          refine ⟨17122942560921595448919059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11415295040614396965946039 17122942560921595448919059)
          ·
            refine ⟨25684413841382393173378589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17122942560921595448919059 25684413841382393173378589)
            ·
              refine ⟨9631655190518397440016971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25684413841382393173378589 9631655190518397440016971)
              ·
                refine ⟨14447482785777596160025457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9631655190518397440016971 14447482785777596160025457)
                ·
                  refine ⟨10835612089333197120019093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14447482785777596160025457 10835612089333197120019093)
                  ·
                    refine ⟨507919316687493615000895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10835612089333197120019093 507919316687493615000895)
                    ·
                      rfl

theorem cell23_2967508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_2967508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967508 prefixEnd_2967508 := by exact prefixLift 2967508
  have htrace : WordTrace (prefixWord ++ tailWord_2967508) baseStart_2967508 baseEnd_2967508 := by
    simpa [prefixWord, tailWord_2967508, baseEnd_2967508] using wordTrace_append hprefix tailTrace_2967508
  have hstable : (prefixWord ++ tailWord_2967508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967508).length < 2 ^ (prefixWord ++ tailWord_2967508).sum := by decide
  have hdescent : baseEnd_2967508 < baseStart_2967508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967521 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 9]
def baseStart_2967521 : Nat := 118140960795 + 2967521 * 2 ^ 59
def prefixEnd_2967521 : Nat := 4983230072969 + 3 ^ 40 * 2967521 * 2
def baseEnd_2967521 : Nat := 169307180590109921571125

theorem tailTrace_2967521 : CollatzResearch.WordTrace tailWord_2967521 prefixEnd_2967521 169307180590109921571125 := by
  unfold tailWord_2967521
  simp only [CollatzResearch.WordTrace]
  refine ⟨108234382682185704082526417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72156255121457136055017611 108234382682185704082526417)
  ·
    refine ⟨81175787011639278061894813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108234382682185704082526417 81175787011639278061894813)
    ·
      refine ⟨30440920129364729273210555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81175787011639278061894813 30440920129364729273210555)
      ·
        refine ⟨45661380194047093909815833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30440920129364729273210555 45661380194047093909815833)
        ·
          refine ⟨34246035145535320432361875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45661380194047093909815833 34246035145535320432361875)
          ·
            refine ⟨51369052718302980648542813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34246035145535320432361875 51369052718302980648542813)
            ·
              refine ⟨19263394769363617743203555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51369052718302980648542813 19263394769363617743203555)
              ·
                refine ⟨28895092154045426614805333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19263394769363617743203555 28895092154045426614805333)
                ·
                  refine ⟨169307180590109921571125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28895092154045426614805333 169307180590109921571125)
                  ·
                    rfl

theorem cell23_2967521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_2967521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967521 prefixEnd_2967521 := by exact prefixLift 2967521
  have htrace : WordTrace (prefixWord ++ tailWord_2967521) baseStart_2967521 baseEnd_2967521 := by
    simpa [prefixWord, tailWord_2967521, baseEnd_2967521] using wordTrace_append hprefix tailTrace_2967521
  have hstable : (prefixWord ++ tailWord_2967521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967521).length < 2 ^ (prefixWord ++ tailWord_2967521).sum := by decide
  have hdescent : baseEnd_2967521 < baseStart_2967521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967548 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_2967548 : Nat := 118140960795 + 2967548 * 2 ^ 59
def prefixEnd_2967548 : Nat := 4983230072969 + 3 ^ 40 * 2967548 * 2
def baseEnd_2967548 : Nat := 1523778489288660688502501

theorem tailTrace_2967548 : CollatzResearch.WordTrace tailWord_2967548 prefixEnd_2967548 1523778489288660688502501 := by
  unfold tailWord_2967548
  simp only [CollatzResearch.WordTrace]
  refine ⟨54117683726543943846879649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72156911635391925129172865 54117683726543943846879649)
  ·
    refine ⟨40588262794907957885159737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54117683726543943846879649 40588262794907957885159737)
    ·
      refine ⟨30441197096180968413869803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40588262794907957885159737 30441197096180968413869803)
      ·
        refine ⟨45661795644271452620804705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30441197096180968413869803 45661795644271452620804705)
        ·
          refine ⟨34246346733203589465603529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45661795644271452620804705 34246346733203589465603529)
          ·
            refine ⟨25684760049902692099202647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34246346733203589465603529 25684760049902692099202647)
            ·
              refine ⟨38527140074854038148803971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25684760049902692099202647 38527140074854038148803971)
              ·
                refine ⟨57790710112281057223205957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38527140074854038148803971 57790710112281057223205957)
                ·
                  refine ⟨10835758146052698229351117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57790710112281057223205957 10835758146052698229351117)
                  ·
                    refine ⟨4063409304769761836006669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10835758146052698229351117 4063409304769761836006669)
                    ·
                      refine ⟨1523778489288660688502501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4063409304769761836006669 1523778489288660688502501)
                      ·
                        rfl

theorem cell23_2967548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_2967548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967548 prefixEnd_2967548 := by exact prefixLift 2967548
  have htrace : WordTrace (prefixWord ++ tailWord_2967548) baseStart_2967548 baseEnd_2967548 := by
    simpa [prefixWord, tailWord_2967548, baseEnd_2967548] using wordTrace_append hprefix tailTrace_2967548
  have hstable : (prefixWord ++ tailWord_2967548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967548).length < 2 ^ (prefixWord ++ tailWord_2967548).sum := by decide
  have hdescent : baseEnd_2967548 < baseStart_2967548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967605 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_2967605 : Nat := 118140960795 + 2967605 * 2 ^ 59
def prefixEnd_2967605 : Nat := 4983230072969 + 3 ^ 40 * 2967605 * 2
def baseEnd_2967605 : Nat := 1523807757685966965489739

theorem tailTrace_2967605 : CollatzResearch.WordTrace tailWord_2967605 prefixEnd_2967605 1523807757685966965489739 := by
  unfold tailWord_2967605
  simp only [CollatzResearch.WordTrace]
  refine ⟨108237446413881386428584269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72158297609254257619056179 108237446413881386428584269)
  ·
    refine ⟨40589042405205519910719101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108237446413881386428584269 40589042405205519910719101)
    ·
      refine ⟨15220890901952069966519663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40589042405205519910719101 15220890901952069966519663)
      ·
        refine ⟨22831336352928104949779495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15220890901952069966519663 22831336352928104949779495)
        ·
          refine ⟨34247004529392157424669243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22831336352928104949779495 34247004529392157424669243)
          ·
            refine ⟨51370506794088236137003865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34247004529392157424669243 51370506794088236137003865)
            ·
              refine ⟨38527880095566177102752899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51370506794088236137003865 38527880095566177102752899)
              ·
                refine ⟨57791820143349265654129349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38527880095566177102752899 57791820143349265654129349)
                ·
                  refine ⟨10835966276877987310149253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57791820143349265654129349 10835966276877987310149253)
                  ·
                    refine ⟨2031743676914622620652985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10835966276877987310149253 2031743676914622620652985)
                    ·
                      refine ⟨1523807757685966965489739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031743676914622620652985 1523807757685966965489739)
                      ·
                        rfl

theorem cell23_2967605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_2967605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967605 prefixEnd_2967605 := by exact prefixLift 2967605
  have htrace : WordTrace (prefixWord ++ tailWord_2967605) baseStart_2967605 baseEnd_2967605 := by
    simpa [prefixWord, tailWord_2967605, baseEnd_2967605] using wordTrace_append hprefix tailTrace_2967605
  have hstable : (prefixWord ++ tailWord_2967605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967605).length < 2 ^ (prefixWord ++ tailWord_2967605).sum := by decide
  have hdescent : baseEnd_2967605 < baseStart_2967605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967615 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 3, 4]
def baseStart_2967615 : Nat := 118140960795 + 2967615 * 2 ^ 59
def prefixEnd_2967615 : Nat := 4983230072969 + 3 ^ 40 * 2967615 * 2
def baseEnd_2967615 : Nat := 507937630830837308788231

theorem tailTrace_2967615 : CollatzResearch.WordTrace tailWord_2967615 prefixEnd_2967615 507937630830837308788231 := by
  unfold tailWord_2967615
  simp only [CollatzResearch.WordTrace]
  refine ⟨108237811143845158136448299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72158540762563438757632199 108237811143845158136448299)
  ·
    refine ⟨162356716715767737204672449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108237811143845158136448299 162356716715767737204672449)
    ·
      refine ⟨121767537536825802903504337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162356716715767737204672449 121767537536825802903504337)
      ·
        refine ⟨91325653152619352177628253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121767537536825802903504337 91325653152619352177628253)
        ·
          refine ⟨34247119932232257066610595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91325653152619352177628253 34247119932232257066610595)
          ·
            refine ⟨51370679898348385599915893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34247119932232257066610595 51370679898348385599915893)
            ·
              refine ⟨4816001240470161149992115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51370679898348385599915893 4816001240470161149992115)
              ·
                refine ⟨7224001860705241724988173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816001240470161149992115 7224001860705241724988173)
                ·
                  refine ⟨2709000697764465646870565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7224001860705241724988173 2709000697764465646870565)
                  ·
                    refine ⟨507937630830837308788231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709000697764465646870565 507937630830837308788231)
                    ·
                      rfl

theorem cell23_2967615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_2967615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967615 prefixEnd_2967615 := by exact prefixLift 2967615
  have htrace : WordTrace (prefixWord ++ tailWord_2967615) baseStart_2967615 baseEnd_2967615 := by
    simpa [prefixWord, tailWord_2967615, baseEnd_2967615] using wordTrace_append hprefix tailTrace_2967615
  have hstable : (prefixWord ++ tailWord_2967615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967615).length < 2 ^ (prefixWord ++ tailWord_2967615).sum := by decide
  have hdescent : baseEnd_2967615 < baseStart_2967615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967622 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2967622 : Nat := 118140960795 + 2967622 * 2 ^ 59
def prefixEnd_2967622 : Nat := 4983230072969 + 3 ^ 40 * 2967622 * 2
def baseEnd_2967622 : Nat := 1523816486857093398977161

theorem tailTrace_2967622 : CollatzResearch.WordTrace tailWord_2967622 prefixEnd_2967622 1523816486857093398977161 := by
  unfold tailWord_2967622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382439576713118697873535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72158710969879865554635413 3382439576713118697873535)
  ·
    refine ⟨5073659365069678046810303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382439576713118697873535 5073659365069678046810303)
    ·
      refine ⟨7610489047604517070215455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073659365069678046810303 7610489047604517070215455)
      ·
        refine ⟨11415733571406775605323183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7610489047604517070215455 11415733571406775605323183)
        ·
          refine ⟨17123600357110163407984775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11415733571406775605323183 17123600357110163407984775)
          ·
            refine ⟨25685400535665245111977163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17123600357110163407984775 25685400535665245111977163)
            ·
              refine ⟨38528100803497867667965745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25685400535665245111977163 38528100803497867667965745)
              ·
                refine ⟨28896075602623400750974309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38528100803497867667965745 28896075602623400750974309)
                ·
                  refine ⟨5418014175491887640807683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28896075602623400750974309 5418014175491887640807683)
                  ·
                    refine ⟨8127021263237831461211525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418014175491887640807683 8127021263237831461211525)
                    ·
                      refine ⟨1523816486857093398977161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8127021263237831461211525 1523816486857093398977161)
                      ·
                        rfl

theorem cell23_2967622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2967622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967622 prefixEnd_2967622 := by exact prefixLift 2967622
  have htrace : WordTrace (prefixWord ++ tailWord_2967622) baseStart_2967622 baseEnd_2967622 := by
    simpa [prefixWord, tailWord_2967622, baseEnd_2967622] using wordTrace_append hprefix tailTrace_2967622
  have hstable : (prefixWord ++ tailWord_2967622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967622).length < 2 ^ (prefixWord ++ tailWord_2967622).sum := by decide
  have hdescent : baseEnd_2967622 < baseStart_2967622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967666 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_2967666 : Nat := 118140960795 + 2967666 * 2 ^ 59
def prefixEnd_2967666 : Nat := 4983230072969 + 3 ^ 40 * 2967666 * 2
def baseEnd_2967666 : Nat := 507946360001963742275653

theorem tailTrace_2967666 : CollatzResearch.WordTrace tailWord_2967666 prefixEnd_2967666 507946360001963742275653 := by
  unfold tailWord_2967666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27059917816665098461638713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72159780844440262564369901 27059917816665098461638713)
  ·
    refine ⟨20294938362498823846229035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27059917816665098461638713 20294938362498823846229035)
    ·
      refine ⟨30442407543748235769343553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20294938362498823846229035 30442407543748235769343553)
      ·
        refine ⟨22831805657811176827007665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30442407543748235769343553 22831805657811176827007665)
        ·
          refine ⟨17123854243358382620255749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22831805657811176827007665 17123854243358382620255749)
          ·
            refine ⟨3210722670629696741297953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17123854243358382620255749 3210722670629696741297953)
            ·
              refine ⟨2408042002972272555973465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210722670629696741297953 2408042002972272555973465)
              ·
                refine ⟨1806031502229204416980099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2408042002972272555973465 1806031502229204416980099)
                ·
                  refine ⟨2709047253343806625470149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806031502229204416980099 2709047253343806625470149)
                  ·
                    refine ⟨507946360001963742275653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709047253343806625470149 507946360001963742275653)
                    ·
                      rfl

theorem cell23_2967666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_2967666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967666 prefixEnd_2967666 := by exact prefixLift 2967666
  have htrace : WordTrace (prefixWord ++ tailWord_2967666) baseStart_2967666 baseEnd_2967666 := by
    simpa [prefixWord, tailWord_2967666, baseEnd_2967666] using wordTrace_append hprefix tailTrace_2967666
  have hstable : (prefixWord ++ tailWord_2967666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967666).length < 2 ^ (prefixWord ++ tailWord_2967666).sum := by decide
  have hdescent : baseEnd_2967666 < baseStart_2967666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967709 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2967709 : Nat := 118140960795 + 2967709 * 2 ^ 59
def prefixEnd_2967709 : Nat := 4983230072969 + 3 ^ 40 * 2967709 * 2
def baseEnd_2967709 : Nat := 507953719891344852863087

theorem tailTrace_2967709 : CollatzResearch.WordTrace tailWord_2967709 prefixEnd_2967709 507953719891344852863087 := by
  unfold tailWord_2967709
  simp only [CollatzResearch.WordTrace]
  refine ⟨108241239605504612190370181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72160826403669741460246787 108241239605504612190370181)
  ·
    refine ⟨20295232426032114785694409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108241239605504612190370181 20295232426032114785694409)
    ·
      refine ⟨15221424319524086089270807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20295232426032114785694409 15221424319524086089270807)
      ·
        refine ⟨22832136479286129133906211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15221424319524086089270807 22832136479286129133906211)
        ·
          refine ⟨34248204718929193700859317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22832136479286129133906211 34248204718929193700859317)
          ·
            refine ⟨3210769192399611909455561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34248204718929193700859317 3210769192399611909455561)
            ·
              refine ⟨2408076894299708932091671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210769192399611909455561 2408076894299708932091671)
              ·
                refine ⟨3612115341449563398137507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408076894299708932091671 3612115341449563398137507)
                ·
                  refine ⟨5418173012174345097206261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612115341449563398137507 5418173012174345097206261)
                  ·
                    refine ⟨507953719891344852863087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5418173012174345097206261 507953719891344852863087)
                    ·
                      rfl

theorem cell23_2967709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2967709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967709 prefixEnd_2967709 := by exact prefixLift 2967709
  have htrace : WordTrace (prefixWord ++ tailWord_2967709) baseStart_2967709 baseEnd_2967709 := by
    simpa [prefixWord, tailWord_2967709, baseEnd_2967709] using wordTrace_append hprefix tailTrace_2967709
  have hstable : (prefixWord ++ tailWord_2967709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967709).length < 2 ^ (prefixWord ++ tailWord_2967709).sum := by decide
  have hdescent : baseEnd_2967709 < baseStart_2967709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967712 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4]
def baseStart_2967712 : Nat := 118140960795 + 2967712 * 2 ^ 59
def prefixEnd_2967712 : Nat := 4983230072969 + 3 ^ 40 * 2967712 * 2
def baseEnd_2967712 : Nat := 1523862700115998046851747

theorem tailTrace_2967712 : CollatzResearch.WordTrace tailWord_2967712 prefixEnd_2967712 1523862700115998046851747 := by
  unfold tailWord_2967712
  simp only [CollatzResearch.WordTrace]
  refine ⟨54120674512246871851364695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72160899349662495801819593 54120674512246871851364695)
  ·
    refine ⟨81181011768370307777047043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54120674512246871851364695 81181011768370307777047043)
    ·
      refine ⟨121771517652555461665570565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81181011768370307777047043 121771517652555461665570565)
      ·
        refine ⟨22832159559854149062294481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121771517652555461665570565 22832159559854149062294481)
        ·
          refine ⟨17124119669890611796720861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22832159559854149062294481 17124119669890611796720861)
          ·
            refine ⟨6421544876208979423770323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17124119669890611796720861 6421544876208979423770323)
            ·
              refine ⟨9632317314313469135655485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421544876208979423770323 9632317314313469135655485)
              ·
                refine ⟨3612118992867550925870807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9632317314313469135655485 3612118992867550925870807)
                ·
                  refine ⟨5418178489301326388806211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612118992867550925870807 5418178489301326388806211)
                  ·
                    refine ⟨8127267733951989583209317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418178489301326388806211 8127267733951989583209317)
                    ·
                      refine ⟨1523862700115998046851747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8127267733951989583209317 1523862700115998046851747)
                      ·
                        rfl

theorem cell23_2967712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_2967712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967712 prefixEnd_2967712 := by exact prefixLift 2967712
  have htrace : WordTrace (prefixWord ++ tailWord_2967712) baseStart_2967712 baseEnd_2967712 := by
    simpa [prefixWord, tailWord_2967712, baseEnd_2967712] using wordTrace_append hprefix tailTrace_2967712
  have hstable : (prefixWord ++ tailWord_2967712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967712).length < 2 ^ (prefixWord ++ tailWord_2967712).sum := by decide
  have hdescent : baseEnd_2967712 < baseStart_2967712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967742 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2967742 : Nat := 118140960795 + 2967742 * 2 ^ 59
def prefixEnd_2967742 : Nat := 4983230072969 + 3 ^ 40 * 2967742 * 2
def baseEnd_2967742 : Nat := 1523878104535632929476609

theorem tailTrace_2967742 : CollatzResearch.WordTrace tailWord_2967742 prefixEnd_2967742 1523878104535632929476609 := by
  unfold tailWord_2967742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13530305401798132353290185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72161628809590039217547653 13530305401798132353290185)
  ·
    refine ⟨10147729051348599264967639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13530305401798132353290185 10147729051348599264967639)
    ·
      refine ⟨15221593577022898897451459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10147729051348599264967639 15221593577022898897451459)
      ·
        refine ⟨22832390365534348346177189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15221593577022898897451459 22832390365534348346177189)
        ·
          refine ⟨4281073193537690314908223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22832390365534348346177189 4281073193537690314908223)
          ·
            refine ⟨6421609790306535472362335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281073193537690314908223 6421609790306535472362335)
            ·
              refine ⟨9632414685459803208543503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421609790306535472362335 9632414685459803208543503)
              ·
                refine ⟨14448622028189704812815255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9632414685459803208543503 14448622028189704812815255)
                ·
                  refine ⟨21672933042284557219222883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14448622028189704812815255 21672933042284557219222883)
                  ·
                    refine ⟨32509399563426835828834325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21672933042284557219222883 32509399563426835828834325)
                    ·
                      refine ⟨1523878104535632929476609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32509399563426835828834325 1523878104535632929476609)
                      ·
                        rfl

theorem cell23_2967742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2967742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967742 prefixEnd_2967742 := by exact prefixLift 2967742
  have htrace : WordTrace (prefixWord ++ tailWord_2967742) baseStart_2967742 baseEnd_2967742 := by
    simpa [prefixWord, tailWord_2967742, baseEnd_2967742] using wordTrace_append hprefix tailTrace_2967742
  have hstable : (prefixWord ++ tailWord_2967742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967742).length < 2 ^ (prefixWord ++ tailWord_2967742).sum := by decide
  have hdescent : baseEnd_2967742 < baseStart_2967742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967746 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2967746 : Nat := 118140960795 + 2967746 * 2 ^ 59
def prefixEnd_2967746 : Nat := 4983230072969 + 3 ^ 40 * 2967746 * 2
def baseEnd_2967746 : Nat := 1523880158458250913826591

theorem tailTrace_2967746 : CollatzResearch.WordTrace tailWord_2967746 prefixEnd_2967746 1523880158458250913826591 := by
  unfold tailWord_2967746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27060647276592641877366773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72161726070913711672978061 27060647276592641877366773)
  ·
    refine ⟨2536935682180560176003135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27060647276592641877366773 2536935682180560176003135)
    ·
      refine ⟨3805403523270840264004703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536935682180560176003135 3805403523270840264004703)
      ·
        refine ⟨5708105284906260396007055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805403523270840264004703 5708105284906260396007055)
        ·
          refine ⟨8562157927359390594010583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708105284906260396007055 8562157927359390594010583)
          ·
            refine ⟨12843236891039085891015875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562157927359390594010583 12843236891039085891015875)
            ·
              refine ⟨19264855336558628836523813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12843236891039085891015875 19264855336558628836523813)
              ·
                refine ⟨3612160375604742906848215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19264855336558628836523813 3612160375604742906848215)
                ·
                  refine ⟨5418240563407114360272323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612160375604742906848215 5418240563407114360272323)
                  ·
                    refine ⟨8127360845110671540408485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418240563407114360272323 8127360845110671540408485)
                    ·
                      refine ⟨1523880158458250913826591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8127360845110671540408485 1523880158458250913826591)
                      ·
                        rfl

theorem cell23_2967746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2967746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967746 prefixEnd_2967746 := by exact prefixLift 2967746
  have htrace : WordTrace (prefixWord ++ tailWord_2967746) baseStart_2967746 baseEnd_2967746 := by
    simpa [prefixWord, tailWord_2967746, baseEnd_2967746] using wordTrace_append hprefix tailTrace_2967746
  have hstable : (prefixWord ++ tailWord_2967746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967746).length < 2 ^ (prefixWord ++ tailWord_2967746).sum := by decide
  have hdescent : baseEnd_2967746 < baseStart_2967746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967766 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2967766 : Nat := 118140960795 + 2967766 * 2 ^ 59
def prefixEnd_2967766 : Nat := 4983230072969 + 3 ^ 40 * 2967766 * 2
def baseEnd_2967766 : Nat := 1523890428071340835576499

theorem tailTrace_2967766 : CollatzResearch.WordTrace tailWord_2967766 prefixEnd_2967766 1523890428071340835576499 := by
  unfold tailWord_2967766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765207410393631932824697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72162212377532073950130101 6765207410393631932824697)
  ·
    refine ⟨5073905557795223949618523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6765207410393631932824697 5073905557795223949618523)
    ·
      refine ⟨7610858336692835924427785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073905557795223949618523 7610858336692835924427785)
      ·
        refine ⟨5708143752519626943320839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7610858336692835924427785 5708143752519626943320839)
        ·
          refine ⟨8562215628779440414981259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708143752519626943320839 8562215628779440414981259)
          ·
            refine ⟨12843323443169160622471889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562215628779440414981259 12843323443169160622471889)
            ·
              refine ⟨9632492582376870466853917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12843323443169160622471889 9632492582376870466853917)
              ·
                refine ⟨3612184718391326425070219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9632492582376870466853917 3612184718391326425070219)
                ·
                  refine ⟨5418277077586989637605329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612184718391326425070219 5418277077586989637605329)
                  ·
                    refine ⟨4063707808190242228203997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5418277077586989637605329 4063707808190242228203997)
                    ·
                      refine ⟨1523890428071340835576499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4063707808190242228203997 1523890428071340835576499)
                      ·
                        rfl

theorem cell23_2967766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2967766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967766 prefixEnd_2967766 := by exact prefixLift 2967766
  have htrace : WordTrace (prefixWord ++ tailWord_2967766) baseStart_2967766 baseEnd_2967766 := by
    simpa [prefixWord, tailWord_2967766, baseEnd_2967766] using wordTrace_append hprefix tailTrace_2967766
  have hstable : (prefixWord ++ tailWord_2967766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967766).length < 2 ^ (prefixWord ++ tailWord_2967766).sum := by decide
  have hdescent : baseEnd_2967766 < baseStart_2967766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967853 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2967853 : Nat := 118140960795 + 2967853 * 2 ^ 59
def prefixEnd_2967853 : Nat := 4983230072969 + 3 ^ 40 * 2967853 * 2
def baseEnd_2967853 : Nat := 1523935100888281995188599

theorem tailTrace_2967853 : CollatzResearch.WordTrace tailWord_2967853 prefixEnd_2967853 1523935100888281995188599 := by
  unfold tailWord_2967853
  simp only [CollatzResearch.WordTrace]
  refine ⟨108246491716982924783612213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72164327811321949855741475 108246491716982924783612213)
  ·
    refine ⟨10148108598467149198463645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108246491716982924783612213 10148108598467149198463645)
    ·
      refine ⟨3805540724425180949423867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10148108598467149198463645 3805540724425180949423867)
      ·
        refine ⟨5708311086637771424135801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805540724425180949423867 5708311086637771424135801)
        ·
          refine ⟨4281233314978328568101851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5708311086637771424135801 4281233314978328568101851)
          ·
            refine ⟨6421849972467492852152777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281233314978328568101851 6421849972467492852152777)
            ·
              refine ⟨4816387479350619639114583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6421849972467492852152777 4816387479350619639114583)
              ·
                refine ⟨7224581219025929458671875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816387479350619639114583 7224581219025929458671875)
                ·
                  refine ⟨10836871828538894188007813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7224581219025929458671875 10836871828538894188007813)
                  ·
                    refine ⟨2031913467851042660251465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10836871828538894188007813 2031913467851042660251465)
                    ·
                      refine ⟨1523935100888281995188599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031913467851042660251465 1523935100888281995188599)
                      ·
                        rfl

theorem cell23_2967853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2967853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967853 prefixEnd_2967853 := by exact prefixLift 2967853
  have htrace : WordTrace (prefixWord ++ tailWord_2967853) baseStart_2967853 baseEnd_2967853 := by
    simpa [prefixWord, tailWord_2967853, baseEnd_2967853] using wordTrace_append hprefix tailTrace_2967853
  have hstable : (prefixWord ++ tailWord_2967853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967853).length < 2 ^ (prefixWord ++ tailWord_2967853).sum := by decide
  have hdescent : baseEnd_2967853 < baseStart_2967853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967855 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 4, 5]
def baseStart_2967855 : Nat := 118140960795 + 2967855 * 2 ^ 59
def prefixEnd_2967855 : Nat := 4983230072969 + 3 ^ 40 * 2967855 * 2
def baseEnd_2967855 : Nat := 507978709283196995787863

theorem tailTrace_2967855 : CollatzResearch.WordTrace tailWord_2967855 prefixEnd_2967855 507978709283196995787863 := by
  unfold tailWord_2967855
  simp only [CollatzResearch.WordTrace]
  refine ⟨108246564662975679125185019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72164376441983786083456679 108246564662975679125185019)
  ·
    refine ⟨162369846994463518687777529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108246564662975679125185019 162369846994463518687777529)
    ·
      refine ⟨121777385245847639015833147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162369846994463518687777529 121777385245847639015833147)
      ·
        refine ⟨182666077868771458523749721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121777385245847639015833147 182666077868771458523749721)
        ·
          refine ⟨136999558401578593892812291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182666077868771458523749721 136999558401578593892812291)
          ·
            refine ⟨205499337602367890839218437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136999558401578593892812291 205499337602367890839218437)
            ·
              refine ⟨38531125800443979532353457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205499337602367890839218437 38531125800443979532353457)
              ·
                refine ⟨28898344350332984649265093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38531125800443979532353457 28898344350332984649265093)
                ·
                  refine ⟨5418439565687434621737205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28898344350332984649265093 5418439565687434621737205)
                  ·
                    refine ⟨507978709283196995787863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5418439565687434621737205 507978709283196995787863)
                    ·
                      rfl

theorem cell23_2967855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_2967855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967855 prefixEnd_2967855 := by exact prefixLift 2967855
  have htrace : WordTrace (prefixWord ++ tailWord_2967855) baseStart_2967855 baseEnd_2967855 := by
    simpa [prefixWord, tailWord_2967855, baseEnd_2967855] using wordTrace_append hprefix tailTrace_2967855
  have hstable : (prefixWord ++ tailWord_2967855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967855).length < 2 ^ (prefixWord ++ tailWord_2967855).sum := by decide
  have hdescent : baseEnd_2967855 < baseStart_2967855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967909 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 2, 4, 2]
def baseStart_2967909 : Nat := 118140960795 + 2967909 * 2 ^ 59
def prefixEnd_2967909 : Nat := 4983230072969 + 3 ^ 40 * 2967909 * 2
def baseEnd_2967909 : Nat := 1523963855804933776088341

theorem tailTrace_2967909 : CollatzResearch.WordTrace tailWord_2967909 prefixEnd_2967909 1523963855804933776088341 := by
  unfold tailWord_2967909
  simp only [CollatzResearch.WordTrace]
  refine ⟨108248534204780046347650781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72165689469853364231767187 108248534204780046347650781)
  ·
    refine ⟨40593200326792517380369043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108248534204780046347650781 40593200326792517380369043)
    ·
      refine ⟨60889800490188776070553565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40593200326792517380369043 60889800490188776070553565)
      ·
        refine ⟨22833675183820791026457587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60889800490188776070553565 22833675183820791026457587)
        ·
          refine ⟨34250512775731186539686381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22833675183820791026457587 34250512775731186539686381)
          ·
            refine ⟨12843942290899194952382393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34250512775731186539686381 12843942290899194952382393)
            ·
              refine ⟨9632956718174396214286795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12843942290899194952382393 9632956718174396214286795)
              ·
                refine ⟨14449435077261594321430193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9632956718174396214286795 14449435077261594321430193)
                ·
                  refine ⟨10837076307946195741072645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14449435077261594321430193 10837076307946195741072645)
                  ·
                    refine ⟨2031951807739911701451121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10837076307946195741072645 2031951807739911701451121)
                    ·
                      refine ⟨1523963855804933776088341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2031951807739911701451121 1523963855804933776088341)
                      ·
                        rfl

theorem cell23_2967909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_2967909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967909 prefixEnd_2967909 := by exact prefixLift 2967909
  have htrace : WordTrace (prefixWord ++ tailWord_2967909) baseStart_2967909 baseEnd_2967909 := by
    simpa [prefixWord, tailWord_2967909, baseEnd_2967909] using wordTrace_append hprefix tailTrace_2967909
  have hstable : (prefixWord ++ tailWord_2967909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967909).length < 2 ^ (prefixWord ++ tailWord_2967909).sum := by decide
  have hdescent : baseEnd_2967909 < baseStart_2967909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967935 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_2967935 : Nat := 118140960795 + 2967935 * 2 ^ 59
def prefixEnd_2967935 : Nat := 4983230072969 + 3 ^ 40 * 2967935 * 2
def baseEnd_2967935 : Nat := 1523977206301950674363221

theorem tailTrace_2967935 : CollatzResearch.WordTrace tailWord_2967935 prefixEnd_2967935 1523977206301950674363221 := by
  unfold tailWord_2967935
  simp only [CollatzResearch.WordTrace]
  refine ⟨108249482502685852788097259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72166321668457235192064839 108249482502685852788097259)
  ·
    refine ⟨162374223754028779182145889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108249482502685852788097259 162374223754028779182145889)
    ·
      refine ⟨121780667815521584386609417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162374223754028779182145889 121780667815521584386609417)
      ·
        refine ⟨91335500861641188289957063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121780667815521584386609417 91335500861641188289957063)
        ·
          refine ⟨137003251292461782434935595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91335500861641188289957063 137003251292461782434935595)
          ·
            refine ⟨205504876938692673652403393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137003251292461782434935595 205504876938692673652403393)
            ·
              refine ⟨154128657704019505239302545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205504876938692673652403393 154128657704019505239302545)
              ·
                refine ⟨115596493278014628929476909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154128657704019505239302545 115596493278014628929476909)
                ·
                  refine ⟨43348684979255485848553841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115596493278014628929476909 43348684979255485848553841)
                  ·
                    refine ⟨32511513734441614386415381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43348684979255485848553841 32511513734441614386415381)
                    ·
                      refine ⟨1523977206301950674363221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32511513734441614386415381 1523977206301950674363221)
                      ·
                        rfl

theorem cell23_2967935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_2967935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967935 prefixEnd_2967935 := by exact prefixLift 2967935
  have htrace : WordTrace (prefixWord ++ tailWord_2967935) baseStart_2967935 baseEnd_2967935 := by
    simpa [prefixWord, tailWord_2967935, baseEnd_2967935] using wordTrace_append hprefix tailTrace_2967935
  have hstable : (prefixWord ++ tailWord_2967935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967935).length < 2 ^ (prefixWord ++ tailWord_2967935).sum := by decide
  have hdescent : baseEnd_2967935 < baseStart_2967935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967966 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2967966 : Nat := 118140960795 + 2967966 * 2 ^ 59
def prefixEnd_2967966 : Nat := 4983230072969 + 3 ^ 40 * 2967966 * 2
def baseEnd_2967966 : Nat := 169332569355804450341731

theorem tailTrace_2967966 : CollatzResearch.WordTrace tailWord_2967966 prefixEnd_2967966 169332569355804450341731 := by
  unfold tailWord_2967966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531326645696693135309469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72167075443715696721650501 13531326645696693135309469)
  ·
    refine ⟨5074247492136259925741051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13531326645696693135309469 5074247492136259925741051)
    ·
      refine ⟨7611371238204389888611577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074247492136259925741051 7611371238204389888611577)
      ·
        refine ⟨5708528428653292416458683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7611371238204389888611577 5708528428653292416458683)
        ·
          refine ⟨8562792642979938624688025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708528428653292416458683 8562792642979938624688025)
          ·
            refine ⟨6422094482234953968516019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8562792642979938624688025 6422094482234953968516019)
            ·
              refine ⟨9633141723352430952774029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422094482234953968516019 9633141723352430952774029)
              ·
                refine ⟨3612428146257161607290261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9633141723352430952774029 3612428146257161607290261)
                ·
                  refine ⟨169332569355804450341731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3612428146257161607290261 169332569355804450341731)
                  ·
                    rfl

theorem cell23_2967966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2967966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967966 prefixEnd_2967966 := by exact prefixLift 2967966
  have htrace : WordTrace (prefixWord ++ tailWord_2967966) baseStart_2967966 baseEnd_2967966 := by
    simpa [prefixWord, tailWord_2967966, baseEnd_2967966] using wordTrace_append hprefix tailTrace_2967966
  have hstable : (prefixWord ++ tailWord_2967966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967966).length < 2 ^ (prefixWord ++ tailWord_2967966).sum := by decide
  have hdescent : baseEnd_2967966 < baseStart_2967966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967986 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_2967986 : Nat := 118140960795 + 2967986 * 2 ^ 59
def prefixEnd_2967986 : Nat := 4983230072969 + 3 ^ 40 * 2967986 * 2
def baseEnd_2967986 : Nat := 1524003393815329974825487

theorem tailTrace_2967986 : CollatzResearch.WordTrace tailWord_2967986 prefixEnd_2967986 1524003393815329974825487 := by
  unfold tailWord_2967986
  simp only [CollatzResearch.WordTrace]
  refine ⟨27062835656375272124550953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72167561750334058998802541 27062835656375272124550953)
  ·
    refine ⟨20297126742281454093413215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27062835656375272124550953 20297126742281454093413215)
    ·
      refine ⟨30445690113422181140119823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297126742281454093413215 30445690113422181140119823)
      ·
        refine ⟨45668535170133271710179735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30445690113422181140119823 45668535170133271710179735)
        ·
          refine ⟨68502802755199907565269603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45668535170133271710179735 68502802755199907565269603)
          ·
            refine ⟨102754204132799861347904405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68502802755199907565269603 102754204132799861347904405)
            ·
              refine ⟨4816603318724993500683019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102754204132799861347904405 4816603318724993500683019)
              ·
                refine ⟨7224904978087490251024529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816603318724993500683019 7224904978087490251024529)
                ·
                  refine ⟨5418678733565617688268397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7224904978087490251024529 5418678733565617688268397)
                  ·
                    refine ⟨2032004525087106633100649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5418678733565617688268397 2032004525087106633100649)
                    ·
                      refine ⟨1524003393815329974825487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032004525087106633100649 1524003393815329974825487)
                      ·
                        rfl

theorem cell23_2967986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_2967986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2967986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2967986 prefixEnd_2967986 := by exact prefixLift 2967986
  have htrace : WordTrace (prefixWord ++ tailWord_2967986) baseStart_2967986 baseEnd_2967986 := by
    simpa [prefixWord, tailWord_2967986, baseEnd_2967986] using wordTrace_append hprefix tailTrace_2967986
  have hstable : (prefixWord ++ tailWord_2967986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967986).length < 2 ^ (prefixWord ++ tailWord_2967986).sum := by decide
  have hdescent : baseEnd_2967986 < baseStart_2967986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968009 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 2, 4]
def baseStart_2968009 : Nat := 118140960795 + 2968009 * 2 ^ 59
def prefixEnd_2968009 : Nat := 4983230072969 + 3 ^ 40 * 2968009 * 2
def baseEnd_2968009 : Nat := 508005067956794461612627

theorem tailTrace_2968009 : CollatzResearch.WordTrace tailWord_2968009 prefixEnd_2968009 508005067956794461612627 := by
  unfold tailWord_2968009
  simp only [CollatzResearch.WordTrace]
  refine ⟨108252181504417763426291081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72168121002945175617527387 108252181504417763426291081)
  ·
    refine ⟨81189136128313322569718311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108252181504417763426291081 81189136128313322569718311)
    ·
      refine ⟨121783704192469983854577467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81189136128313322569718311 121783704192469983854577467)
      ·
        refine ⟨182675556288704975781866201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121783704192469983854577467 182675556288704975781866201)
        ·
          refine ⟨137006667216528731836399651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182675556288704975781866201 137006667216528731836399651)
          ·
            refine ⟨205510000824793097754599477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137006667216528731836399651 205510000824793097754599477)
            ·
              refine ⟨19266562577324352914493701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205510000824793097754599477 19266562577324352914493701)
              ·
                refine ⟨3612480483248316171467569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19266562577324352914493701 3612480483248316171467569)
                ·
                  refine ⟨2709360362436237128600677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612480483248316171467569 2709360362436237128600677)
                  ·
                    refine ⟨508005067956794461612627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709360362436237128600677 508005067956794461612627)
                    ·
                      rfl

theorem cell23_2968009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_2968009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968009 prefixEnd_2968009 := by exact prefixLift 2968009
  have htrace : WordTrace (prefixWord ++ tailWord_2968009) baseStart_2968009 baseEnd_2968009 := by
    simpa [prefixWord, tailWord_2968009, baseEnd_2968009] using wordTrace_append hprefix tailTrace_2968009
  have hstable : (prefixWord ++ tailWord_2968009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968009).length < 2 ^ (prefixWord ++ tailWord_2968009).sum := by decide
  have hdescent : baseEnd_2968009 < baseStart_2968009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968039 : List Nat := [1, 1, 5, 2, 1, 1, 5, 7]
def baseStart_2968039 : Nat := 118140960795 + 2968039 * 2 ^ 59
def prefixEnd_2968039 : Nat := 4983230072969 + 3 ^ 40 * 2968039 * 2
def baseEnd_2968039 : Nat := 56445578084815491387509

theorem tailTrace_2968039 : CollatzResearch.WordTrace tailWord_2968039 prefixEnd_2968039 56445578084815491387509 := by
  unfold tailWord_2968039
  simp only [CollatzResearch.WordTrace]
  refine ⟨108253275694309078549883171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72168850462872719033255447 108253275694309078549883171)
  ·
    refine ⟨162379913541463617824824757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108253275694309078549883171 162379913541463617824824757)
    ·
      refine ⟨15223116894512214171077321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162379913541463617824824757 15223116894512214171077321)
      ·
        refine ⟨11417337670884160628307991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15223116894512214171077321 11417337670884160628307991)
        ·
          refine ⟨17126006506326240942461987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417337670884160628307991 17126006506326240942461987)
          ·
            refine ⟨25689009759489361413692981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17126006506326240942461987 25689009759489361413692981)
            ·
              refine ⟨2408344664952127632533717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25689009759489361413692981 2408344664952127632533717)
              ·
                refine ⟨56445578084815491387509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2408344664952127632533717 56445578084815491387509)
                ·
                  rfl

theorem cell23_2968039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 7].length) (baseStart_2968039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968039 prefixEnd_2968039 := by exact prefixLift 2968039
  have htrace : WordTrace (prefixWord ++ tailWord_2968039) baseStart_2968039 baseEnd_2968039 := by
    simpa [prefixWord, tailWord_2968039, baseEnd_2968039] using wordTrace_append hprefix tailTrace_2968039
  have hstable : (prefixWord ++ tailWord_2968039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968039).length < 2 ^ (prefixWord ++ tailWord_2968039).sum := by decide
  have hdescent : baseEnd_2968039 < baseStart_2968039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968049 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_2968049 : Nat := 118140960795 + 2968049 * 2 ^ 59
def prefixEnd_2968049 : Nat := 4983230072969 + 3 ^ 40 * 2968049 * 2
def baseEnd_2968049 : Nat := 1524035743096563228337697

theorem tailTrace_2968049 : CollatzResearch.WordTrace tailWord_2968049 prefixEnd_2968049 1524035743096563228337697 := by
  unfold tailWord_2968049
  simp only [CollatzResearch.WordTrace]
  refine ⟨108253640424272850257747201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72169093616181900171831467 108253640424272850257747201)
  ·
    refine ⟨81190230318204637693310401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108253640424272850257747201 81190230318204637693310401)
    ·
      refine ⟨60892672738653478269982801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81190230318204637693310401 60892672738653478269982801)
      ·
        refine ⟨45669504553990108702487101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60892672738653478269982801 45669504553990108702487101)
        ·
          refine ⟨17126064207746290763432663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45669504553990108702487101 17126064207746290763432663)
          ·
            refine ⟨25689096311619436145148995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17126064207746290763432663 25689096311619436145148995)
            ·
              refine ⟨38533644467429154217723493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25689096311619436145148995 38533644467429154217723493)
              ·
                refine ⟨7225058337642966415823155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38533644467429154217723493 7225058337642966415823155)
                ·
                  refine ⟨10837587506464449623734733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7225058337642966415823155 10837587506464449623734733)
                  ·
                    refine ⟨4064095314924168608900525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10837587506464449623734733 4064095314924168608900525)
                    ·
                      refine ⟨1524035743096563228337697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064095314924168608900525 1524035743096563228337697)
                      ·
                        rfl

theorem cell23_2968049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_2968049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968049 prefixEnd_2968049 := by exact prefixLift 2968049
  have htrace : WordTrace (prefixWord ++ tailWord_2968049) baseStart_2968049 baseEnd_2968049 := by
    simpa [prefixWord, tailWord_2968049, baseEnd_2968049] using wordTrace_append hprefix tailTrace_2968049
  have hstable : (prefixWord ++ tailWord_2968049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968049).length < 2 ^ (prefixWord ++ tailWord_2968049).sum := by decide
  have hdescent : baseEnd_2968049 < baseStart_2968049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968050 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_2968050 : Nat := 118140960795 + 2968050 * 2 ^ 59
def prefixEnd_2968050 : Nat := 4983230072969 + 3 ^ 40 * 2968050 * 2
def baseEnd_2968050 : Nat := 1524036256577217724425193

theorem tailTrace_2968050 : CollatzResearch.WordTrace tailWord_2968050 prefixEnd_2968050 1524036256577217724425193 := by
  unfold tailWord_2968050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27063419224317306857133401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72169117931512818285689069 27063419224317306857133401)
  ·
    refine ⟨20297564418237980142850051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27063419224317306857133401 20297564418237980142850051)
    ·
      refine ⟨30446346627356970214275077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297564418237980142850051 30446346627356970214275077)
      ·
        refine ⟨5708689992629431915176577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30446346627356970214275077 5708689992629431915176577)
        ·
          refine ⟨4281517494472073936382433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5708689992629431915176577 4281517494472073936382433)
          ·
            refine ⟨3211138120854055452286825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4281517494472073936382433 3211138120854055452286825)
            ·
              refine ⟨2408353590640541589215119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211138120854055452286825 2408353590640541589215119)
              ·
                refine ⟨3612530385960812383822679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408353590640541589215119 3612530385960812383822679)
                ·
                  refine ⟨5418795578941218575734019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612530385960812383822679 5418795578941218575734019)
                  ·
                    refine ⟨8128193368411827863601029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418795578941218575734019 8128193368411827863601029)
                    ·
                      refine ⟨1524036256577217724425193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8128193368411827863601029 1524036256577217724425193)
                      ·
                        rfl

theorem cell23_2968050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_2968050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968050 prefixEnd_2968050 := by exact prefixLift 2968050
  have htrace : WordTrace (prefixWord ++ tailWord_2968050) baseStart_2968050 baseEnd_2968050 := by
    simpa [prefixWord, tailWord_2968050, baseEnd_2968050] using wordTrace_append hprefix tailTrace_2968050
  have hstable : (prefixWord ++ tailWord_2968050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968050).length < 2 ^ (prefixWord ++ tailWord_2968050).sum := by decide
  have hdescent : baseEnd_2968050 < baseStart_2968050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968070 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2968070 : Nat := 118140960795 + 2968070 * 2 ^ 59
def prefixEnd_2968070 : Nat := 4983230072969 + 3 ^ 40 * 2968070 * 2
def baseEnd_2968070 : Nat := 1524046526190307646175101

theorem tailTrace_2968070 : CollatzResearch.WordTrace tailWord_2968070 prefixEnd_2968070 1524046526190307646175101 := by
  unfold tailWord_2968070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382950198662399088883177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72169604238131180562841109 3382950198662399088883177)
  ·
    refine ⟨2537212648996799316662383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3382950198662399088883177 2537212648996799316662383)
    ·
      refine ⟨3805818973495198974993575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537212648996799316662383 3805818973495198974993575)
      ·
        refine ⟨5708728460242798462490363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805818973495198974993575 5708728460242798462490363)
        ·
          refine ⟨8563092690364197693735545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708728460242798462490363 8563092690364197693735545)
          ·
            refine ⟨6422319517773148270301659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8563092690364197693735545 6422319517773148270301659)
            ·
              refine ⟨9633479276659722405452489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422319517773148270301659 9633479276659722405452489)
              ·
                refine ⟨7225109457494791804089367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9633479276659722405452489 7225109457494791804089367)
                ·
                  refine ⟨10837664186242187706134051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7225109457494791804089367 10837664186242187706134051)
                  ·
                    refine ⟨16256496279363281559201077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10837664186242187706134051 16256496279363281559201077)
                    ·
                      refine ⟨1524046526190307646175101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16256496279363281559201077 1524046526190307646175101)
                      ·
                        rfl

theorem cell23_2968070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2968070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968070 prefixEnd_2968070 := by exact prefixLift 2968070
  have htrace : WordTrace (prefixWord ++ tailWord_2968070) baseStart_2968070 baseEnd_2968070 := by
    simpa [prefixWord, tailWord_2968070, baseEnd_2968070] using wordTrace_append hprefix tailTrace_2968070
  have hstable : (prefixWord ++ tailWord_2968070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968070).length < 2 ^ (prefixWord ++ tailWord_2968070).sum := by decide
  have hdescent : baseEnd_2968070 < baseStart_2968070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968077 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2968077 : Nat := 118140960795 + 2968077 * 2 ^ 59
def prefixEnd_2968077 : Nat := 4983230072969 + 3 ^ 40 * 2968077 * 2
def baseEnd_2968077 : Nat := 508016706851629706262523

theorem tailTrace_2968077 : CollatzResearch.WordTrace tailWord_2968077 prefixEnd_2968077 508016706851629706262523 := by
  unfold tailWord_2968077
  simp only [CollatzResearch.WordTrace]
  refine ⟨108254661668171411039766485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72169774445447607359844323 108254661668171411039766485)
  ·
    refine ⟨2537218632847767446244527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 108254661668171411039766485 2537218632847767446244527)
    ·
      refine ⟨3805827949271651169366791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537218632847767446244527 3805827949271651169366791)
      ·
        refine ⟨5708741923907476754050187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805827949271651169366791 5708741923907476754050187)
        ·
          refine ⟨8563112885861215131075281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708741923907476754050187 8563112885861215131075281)
          ·
            refine ⟨6422334664395911348306461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8563112885861215131075281 6422334664395911348306461)
            ·
              refine ⟨2408375499148466755614923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6422334664395911348306461 2408375499148466755614923)
              ·
                refine ⟨3612563248722700133422385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408375499148466755614923 3612563248722700133422385)
                ·
                  refine ⟨2709422436542025100066789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612563248722700133422385 2709422436542025100066789)
                  ·
                    refine ⟨508016706851629706262523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709422436542025100066789 508016706851629706262523)
                    ·
                      rfl

theorem cell23_2968077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2968077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968077 prefixEnd_2968077 := by exact prefixLift 2968077
  have htrace : WordTrace (prefixWord ++ tailWord_2968077) baseStart_2968077 baseEnd_2968077 := by
    simpa [prefixWord, tailWord_2968077, baseEnd_2968077] using wordTrace_append hprefix tailTrace_2968077
  have hstable : (prefixWord ++ tailWord_2968077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968077).length < 2 ^ (prefixWord ++ tailWord_2968077).sum := by decide
  have hdescent : baseEnd_2968077 < baseStart_2968077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968083 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 2, 1, 3]
def baseStart_2968083 : Nat := 118140960795 + 2968083 * 2 ^ 59
def prefixEnd_2968083 : Nat := 4983230072969 + 3 ^ 40 * 2968083 * 2
def baseEnd_2968083 : Nat := 1524053201438816095312541

theorem tailTrace_2968083 : CollatzResearch.WordTrace tailWord_2968083 prefixEnd_2968083 1524053201438816095312541 := by
  unfold tailWord_2968083
  simp only [CollatzResearch.WordTrace]
  refine ⟨108254880506149674064484903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72169920337433116042989935 108254880506149674064484903)
  ·
    refine ⟨162382320759224511096727355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108254880506149674064484903 162382320759224511096727355)
    ·
      refine ⟨243573481138836766645091033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162382320759224511096727355 243573481138836766645091033)
      ·
        refine ⟨182680110854127574983818275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243573481138836766645091033 182680110854127574983818275)
        ·
          refine ⟨274020166281191362475727413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182680110854127574983818275 274020166281191362475727413)
          ·
            refine ⟨25689390588861690232099445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274020166281191362475727413 25689390588861690232099445)
            ·
              refine ⟨2408380367705783459259323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25689390588861690232099445 2408380367705783459259323)
              ·
                refine ⟨3612570551558675188888985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408380367705783459259323 3612570551558675188888985)
                ·
                  refine ⟨2709427913669006391666739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612570551558675188888985 2709427913669006391666739)
                  ·
                    refine ⟨4064141870503509587500109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2709427913669006391666739 4064141870503509587500109)
                    ·
                      refine ⟨1524053201438816095312541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064141870503509587500109 1524053201438816095312541)
                      ·
                        rfl

theorem cell23_2968083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 1, 3].length) (baseStart_2968083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968083 prefixEnd_2968083 := by exact prefixLift 2968083
  have htrace : WordTrace (prefixWord ++ tailWord_2968083) baseStart_2968083 baseEnd_2968083 := by
    simpa [prefixWord, tailWord_2968083, baseEnd_2968083] using wordTrace_append hprefix tailTrace_2968083
  have hstable : (prefixWord ++ tailWord_2968083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968083).length < 2 ^ (prefixWord ++ tailWord_2968083).sum := by decide
  have hdescent : baseEnd_2968083 < baseStart_2968083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968093 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_2968093 : Nat := 118140960795 + 2968093 * 2 ^ 59
def prefixEnd_2968093 : Nat := 4983230072969 + 3 ^ 40 * 2968093 * 2
def baseEnd_2968093 : Nat := 1524058336245361056187495

theorem tailTrace_2968093 : CollatzResearch.WordTrace tailWord_2968093 prefixEnd_2968093 1524058336245361056187495 := by
  unfold tailWord_2968093
  simp only [CollatzResearch.WordTrace]
  refine ⟨108255245236113445772348933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72170163490742297181565955 108255245236113445772348933)
  ·
    refine ⟨20297858481771271082315425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108255245236113445772348933 20297858481771271082315425)
    ·
      refine ⟨15223393861328453311736569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20297858481771271082315425 15223393861328453311736569)
      ·
        refine ⟨11417545395996339983802427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15223393861328453311736569 11417545395996339983802427)
        ·
          refine ⟨17126318093994509975703641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417545395996339983802427 17126318093994509975703641)
          ·
            refine ⟨12844738570495882481777731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17126318093994509975703641 12844738570495882481777731)
            ·
              refine ⟨19267107855743823722666597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12844738570495882481777731 19267107855743823722666597)
              ·
                refine ⟨3612582722951966947999987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19267107855743823722666597 3612582722951966947999987)
                ·
                  refine ⟨5418874084427950421999981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612582722951966947999987 5418874084427950421999981)
                  ·
                    refine ⟨2032077781660481408249993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5418874084427950421999981 2032077781660481408249993)
                    ·
                      refine ⟨1524058336245361056187495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032077781660481408249993 1524058336245361056187495)
                      ·
                        rfl

theorem cell23_2968093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_2968093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968093 prefixEnd_2968093 := by exact prefixLift 2968093
  have htrace : WordTrace (prefixWord ++ tailWord_2968093) baseStart_2968093 baseEnd_2968093 := by
    simpa [prefixWord, tailWord_2968093, baseEnd_2968093] using wordTrace_append hprefix tailTrace_2968093
  have hstable : (prefixWord ++ tailWord_2968093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968093).length < 2 ^ (prefixWord ++ tailWord_2968093).sum := by decide
  have hdescent : baseEnd_2968093 < baseStart_2968093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968112 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 9]
def baseStart_2968112 : Nat := 118140960795 + 2968112 * 2 ^ 59
def prefixEnd_2968112 : Nat := 4983230072969 + 3 ^ 40 * 2968112 * 2
def baseEnd_2968112 : Nat := 169340899153088497983323

theorem tailTrace_2968112 : CollatzResearch.WordTrace tailWord_2968112 prefixEnd_2968112 169340899153088497983323 := by
  unfold tailWord_2968112
  simp only [CollatzResearch.WordTrace]
  refine ⟨54127969111522306008645295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72170625482029741344860393 54127969111522306008645295)
  ·
    refine ⟨81191953667283459012967943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54127969111522306008645295 81191953667283459012967943)
    ·
      refine ⟨121787930500925188519451915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81191953667283459012967943 121787930500925188519451915)
      ·
        refine ⟨182681895751387782779177873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121787930500925188519451915 182681895751387782779177873)
        ·
          refine ⟨137011421813540837084383405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182681895751387782779177873 137011421813540837084383405)
          ·
            refine ⟨51379283180077813906643777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137011421813540837084383405 51379283180077813906643777)
            ·
              refine ⟨38534462385058360429982833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51379283180077813906643777 38534462385058360429982833)
              ·
                refine ⟨28900846788793770322487125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38534462385058360429982833 28900846788793770322487125)
                ·
                  refine ⟨169340899153088497983323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28900846788793770322487125 169340899153088497983323)
                  ·
                    rfl

theorem cell23_2968112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_2968112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968112 prefixEnd_2968112 := by exact prefixLift 2968112
  have htrace : WordTrace (prefixWord ++ tailWord_2968112) baseStart_2968112 baseEnd_2968112 := by
    simpa [prefixWord, tailWord_2968112, baseEnd_2968112] using wordTrace_append hprefix tailTrace_2968112
  have hstable : (prefixWord ++ tailWord_2968112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968112).length < 2 ^ (prefixWord ++ tailWord_2968112).sum := by decide
  have hdescent : baseEnd_2968112 < baseStart_2968112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968134 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2968134 : Nat := 118140960795 + 2968134 * 2 ^ 59
def prefixEnd_2968134 : Nat := 4983230072969 + 3 ^ 40 * 2968134 * 2
def baseEnd_2968134 : Nat := 1524079388952195395774807

theorem tailTrace_2968134 : CollatzResearch.WordTrace tailWord_2968134 prefixEnd_2968134 1524079388952195395774807 := by
  unfold tailWord_2968134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383023144655153430455983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72171160419309939849727637 3383023144655153430455983)
  ·
    refine ⟨5074534716982730145683975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383023144655153430455983 5074534716982730145683975)
    ·
      refine ⟨7611802075474095218525963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074534716982730145683975 7611802075474095218525963)
      ·
        refine ⟨11417703113211142827788945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611802075474095218525963 11417703113211142827788945)
        ·
          refine ⟨8563277334908357120841709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11417703113211142827788945 8563277334908357120841709)
          ·
            refine ⟨3211229000590633920315641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8563277334908357120841709 3211229000590633920315641)
            ·
              refine ⟨2408421750442975440236731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211229000590633920315641 2408421750442975440236731)
              ·
                refine ⟨3612632625664463160355097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408421750442975440236731 3612632625664463160355097)
                ·
                  refine ⟨2709474469248347370266323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612632625664463160355097 2709474469248347370266323)
                  ·
                    refine ⟨4064211703872521055399485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2709474469248347370266323 4064211703872521055399485)
                    ·
                      refine ⟨1524079388952195395774807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064211703872521055399485 1524079388952195395774807)
                      ·
                        rfl

theorem cell23_2968134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2968134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968134 prefixEnd_2968134 := by exact prefixLift 2968134
  have htrace : WordTrace (prefixWord ++ tailWord_2968134) baseStart_2968134 baseEnd_2968134 := by
    simpa [prefixWord, tailWord_2968134, baseEnd_2968134] using wordTrace_append hprefix tailTrace_2968134
  have hstable : (prefixWord ++ tailWord_2968134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968134).length < 2 ^ (prefixWord ++ tailWord_2968134).sum := by decide
  have hdescent : baseEnd_2968134 < baseStart_2968134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968139 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 3]
def baseStart_2968139 : Nat := 118140960795 + 2968139 * 2 ^ 59
def prefixEnd_2968139 : Nat := 4983230072969 + 3 ^ 40 * 2968139 * 2
def baseEnd_2968139 : Nat := 1524081956355467876212283

theorem tailTrace_2968139 : CollatzResearch.WordTrace tailWord_2968139 prefixEnd_2968139 1524081956355467876212283 := by
  unfold tailWord_2968139
  simp only [CollatzResearch.WordTrace]
  refine ⟨108256922993946795628523471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72171281995964530419015647 108256922993946795628523471)
  ·
    refine ⟨162385384490920193442785207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108256922993946795628523471 162385384490920193442785207)
    ·
      refine ⟨243578076736380290164177811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162385384490920193442785207 243578076736380290164177811)
      ·
        refine ⟨365367115104570435246266717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243578076736380290164177811 365367115104570435246266717)
        ·
          refine ⟨137012668164213913217350019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365367115104570435246266717 137012668164213913217350019)
          ·
            refine ⟨205519002246320869826025029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137012668164213913217350019 205519002246320869826025029)
            ·
              refine ⟨38534812921185163092379693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205519002246320869826025029 38534812921185163092379693)
              ·
                refine ⟨14450554845444436159642385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38534812921185163092379693 14450554845444436159642385)
                ·
                  refine ⟨10837916134083327119731789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14450554845444436159642385 10837916134083327119731789)
                  ·
                    refine ⟨4064218550281247669899421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10837916134083327119731789 4064218550281247669899421)
                    ·
                      refine ⟨1524081956355467876212283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064218550281247669899421 1524081956355467876212283)
                      ·
                        rfl

theorem cell23_2968139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 3].length) (baseStart_2968139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968139 prefixEnd_2968139 := by exact prefixLift 2968139
  have htrace : WordTrace (prefixWord ++ tailWord_2968139) baseStart_2968139 baseEnd_2968139 := by
    simpa [prefixWord, tailWord_2968139, baseEnd_2968139] using wordTrace_append hprefix tailTrace_2968139
  have hstable : (prefixWord ++ tailWord_2968139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968139).length < 2 ^ (prefixWord ++ tailWord_2968139).sum := by decide
  have hdescent : baseEnd_2968139 < baseStart_2968139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968179 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 4]
def baseStart_2968179 : Nat := 118140960795 + 2968179 * 2 ^ 59
def prefixEnd_2968179 : Nat := 4983230072969 + 3 ^ 40 * 2968179 * 2
def baseEnd_2968179 : Nat := 1524102495581647719712099

theorem tailTrace_2968179 : CollatzResearch.WordTrace tailWord_2968179 prefixEnd_2968179 1524102495581647719712099 := by
  unfold tailWord_2968179
  simp only [CollatzResearch.WordTrace]
  refine ⟨108258381913801882459979591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72172254609201254973319727 108258381913801882459979591)
  ·
    refine ⟨162387572870702823689969387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108258381913801882459979591 162387572870702823689969387)
    ·
      refine ⟨243581359306054235534954081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162387572870702823689969387 243581359306054235534954081)
      ·
        refine ⟨182686019479540676651215561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243581359306054235534954081 182686019479540676651215561)
        ·
          refine ⟨137014514609655507488411671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182686019479540676651215561 137014514609655507488411671)
          ·
            refine ⟨205521771914483261232617507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137014514609655507488411671 205521771914483261232617507)
            ·
              refine ⟨308282657871724891848926261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205521771914483261232617507 308282657871724891848926261)
              ·
                refine ⟨28901499175474208610836837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308282657871724891848926261 28901499175474208610836837)
                ·
                  refine ⟨5419031095401414114531907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28901499175474208610836837 5419031095401414114531907)
                  ·
                    refine ⟨8128546643102121171797861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5419031095401414114531907 8128546643102121171797861)
                    ·
                      refine ⟨1524102495581647719712099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8128546643102121171797861 1524102495581647719712099)
                      ·
                        rfl

theorem cell23_2968179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_2968179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968179 prefixEnd_2968179 := by exact prefixLift 2968179
  have htrace : WordTrace (prefixWord ++ tailWord_2968179) baseStart_2968179 baseEnd_2968179 := by
    simpa [prefixWord, tailWord_2968179, baseEnd_2968179] using wordTrace_append hprefix tailTrace_2968179
  have hstable : (prefixWord ++ tailWord_2968179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968179).length < 2 ^ (prefixWord ++ tailWord_2968179).sum := by decide
  have hdescent : baseEnd_2968179 < baseStart_2968179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968216 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2968216 : Nat := 118140960795 + 2968216 * 2 ^ 59
def prefixEnd_2968216 : Nat := 4983230072969 + 3 ^ 40 * 2968216 * 2
def baseEnd_2968216 : Nat := 1524121494365864074949429

theorem tailTrace_2968216 : CollatzResearch.WordTrace tailWord_2968216 prefixEnd_2968216 1524121494365864074949429 := by
  unfold tailWord_2968216
  simp only [CollatzResearch.WordTrace]
  refine ⟨54129865707333918889538251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72173154276445225186051001 54129865707333918889538251)
  ·
    refine ⟨81194798561000878334307377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54129865707333918889538251 81194798561000878334307377)
    ·
      refine ⟨60896098920750658750730533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81194798561000878334307377 60896098920750658750730533)
      ·
        refine ⟨11418018547640748515761975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60896098920750658750730533 11418018547640748515761975)
        ·
          refine ⟨17127027821461122773642963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11418018547640748515761975 17127027821461122773642963)
          ·
            refine ⟨25690541732191684160464445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17127027821461122773642963 25690541732191684160464445)
            ·
              refine ⟨9633953149571881560174167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25690541732191684160464445 9633953149571881560174167)
              ·
                refine ⟨14450929724357822340261251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633953149571881560174167 14450929724357822340261251)
                ·
                  refine ⟨21676394586536733510391877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14450929724357822340261251 21676394586536733510391877)
                  ·
                    refine ⟨4064323984975637533198477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21676394586536733510391877 4064323984975637533198477)
                    ·
                      refine ⟨1524121494365864074949429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064323984975637533198477 1524121494365864074949429)
                      ·
                        rfl

theorem cell23_2968216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2968216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968216 prefixEnd_2968216 := by exact prefixLift 2968216
  have htrace : WordTrace (prefixWord ++ tailWord_2968216) baseStart_2968216 baseEnd_2968216 := by
    simpa [prefixWord, tailWord_2968216, baseEnd_2968216] using wordTrace_append hprefix tailTrace_2968216
  have hstable : (prefixWord ++ tailWord_2968216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968216).length < 2 ^ (prefixWord ++ tailWord_2968216).sum := by decide
  have hdescent : baseEnd_2968216 < baseStart_2968216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968239 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_2968239 : Nat := 118140960795 + 2968239 * 2 ^ 59
def prefixEnd_2968239 : Nat := 4983230072969 + 3 ^ 40 * 2968239 * 2
def baseEnd_2968239 : Nat := 1524133304420917484961823

theorem tailTrace_2968239 : CollatzResearch.WordTrace tailWord_2968239 prefixEnd_2968239 1524133304420917484961823 := by
  unfold tailWord_2968239
  simp only [CollatzResearch.WordTrace]
  refine ⟨108260570293584512707163771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72173713529056341804775847 108260570293584512707163771)
  ·
    refine ⟨162390855440376769060745657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108260570293584512707163771 162390855440376769060745657)
    ·
      refine ⟨121793141580282576795559243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162390855440376769060745657 121793141580282576795559243)
      ·
        refine ⟨182689712370423865193338865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121793141580282576795559243 182689712370423865193338865)
        ·
          refine ⟨137017284277817898895004149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182689712370423865193338865 137017284277817898895004149)
          ·
            refine ⟨12845370401045428021406639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137017284277817898895004149 12845370401045428021406639)
            ·
              refine ⟨19268055601568142032109959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12845370401045428021406639 19268055601568142032109959)
              ·
                refine ⟨28902083402352213048164939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19268055601568142032109959 28902083402352213048164939)
                ·
                  refine ⟨43353125103528319572247409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28902083402352213048164939 43353125103528319572247409)
                  ·
                    refine ⟨32514843827646239679185557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43353125103528319572247409 32514843827646239679185557)
                    ·
                      refine ⟨1524133304420917484961823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32514843827646239679185557 1524133304420917484961823)
                      ·
                        rfl

theorem cell23_2968239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_2968239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968239 prefixEnd_2968239 := by exact prefixLift 2968239
  have htrace : WordTrace (prefixWord ++ tailWord_2968239) baseStart_2968239 baseEnd_2968239 := by
    simpa [prefixWord, tailWord_2968239, baseEnd_2968239] using wordTrace_append hprefix tailTrace_2968239
  have hstable : (prefixWord ++ tailWord_2968239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968239).length < 2 ^ (prefixWord ++ tailWord_2968239).sum := by decide
  have hdescent : baseEnd_2968239 < baseStart_2968239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968253 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 6]
def baseStart_2968253 : Nat := 118140960795 + 2968253 * 2 ^ 59
def prefixEnd_2968253 : Nat := 4983230072969 + 3 ^ 40 * 2968253 * 2
def baseEnd_2968253 : Nat := 169348943683342270020751

theorem tailTrace_2968253 : CollatzResearch.WordTrace tailWord_2968253 prefixEnd_2968253 169348943683342270020751 := by
  unfold tailWord_2968253
  simp only [CollatzResearch.WordTrace]
  refine ⟨108261080915533793098173413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72174053943689195398782275 108261080915533793098173413)
  ·
    refine ⟨20298952671662586205907515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108261080915533793098173413 20298952671662586205907515)
    ·
      refine ⟨30448429007493879308861273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20298952671662586205907515 30448429007493879308861273)
      ·
        refine ⟨22836321755620409481645955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30448429007493879308861273 22836321755620409481645955)
        ·
          refine ⟨34254482633430614222468933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22836321755620409481645955 34254482633430614222468933)
          ·
            refine ⟨6422715493768240166712925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34254482633430614222468933 6422715493768240166712925)
            ·
              refine ⟨2408518310163090062517347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6422715493768240166712925 2408518310163090062517347)
              ·
                refine ⟨3612777465244635093776021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408518310163090062517347 3612777465244635093776021)
                ·
                  refine ⟨169348943683342270020751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3612777465244635093776021 169348943683342270020751)
                  ·
                    rfl

theorem cell23_2968253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_2968253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968253 prefixEnd_2968253 := by exact prefixLift 2968253
  have htrace : WordTrace (prefixWord ++ tailWord_2968253) baseStart_2968253 baseEnd_2968253 := by
    simpa [prefixWord, tailWord_2968253, baseEnd_2968253] using wordTrace_append hprefix tailTrace_2968253
  have hstable : (prefixWord ++ tailWord_2968253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968253).length < 2 ^ (prefixWord ++ tailWord_2968253).sum := by decide
  have hdescent : baseEnd_2968253 < baseStart_2968253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968273 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 2, 3, 2]
def baseStart_2968273 : Nat := 118140960795 + 2968273 * 2 ^ 59
def prefixEnd_2968273 : Nat := 4983230072969 + 3 ^ 40 * 2968273 * 2
def baseEnd_2968273 : Nat := 1524150762763170351936667

theorem tailTrace_2968273 : CollatzResearch.WordTrace tailWord_2968273 prefixEnd_2968273 1524150762763170351936667 := by
  unfold tailWord_2968273
  simp only [CollatzResearch.WordTrace]
  refine ⟨108261810375461336513901473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72174540250307557675934315 108261810375461336513901473)
  ·
    refine ⟨81196357781596002385426105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108261810375461336513901473 81196357781596002385426105)
    ·
      refine ⟨60897268336197001789069579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81196357781596002385426105 60897268336197001789069579)
      ·
        refine ⟨91345902504295502683604369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60897268336197001789069579 91345902504295502683604369)
        ·
          refine ⟨68509426878221627012703277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91345902504295502683604369 68509426878221627012703277)
          ·
            refine ⟨25691035079333110129763729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68509426878221627012703277 25691035079333110129763729)
            ·
              refine ⟨19268276309499832597322797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25691035079333110129763729 19268276309499832597322797)
              ·
                refine ⟨7225603616062437223996049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19268276309499832597322797 7225603616062437223996049)
                ·
                  refine ⟨5419202712046827917997037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7225603616062437223996049 5419202712046827917997037)
                  ·
                    refine ⟨2032201017017560469248889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5419202712046827917997037 2032201017017560469248889)
                    ·
                      refine ⟨1524150762763170351936667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032201017017560469248889 1524150762763170351936667)
                      ·
                        rfl

theorem cell23_2968273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_2968273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968273 prefixEnd_2968273 := by exact prefixLift 2968273
  have htrace : WordTrace (prefixWord ++ tailWord_2968273) baseStart_2968273 baseEnd_2968273 := by
    simpa [prefixWord, tailWord_2968273, baseEnd_2968273] using wordTrace_append hprefix tailTrace_2968273
  have hstable : (prefixWord ++ tailWord_2968273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968273).length < 2 ^ (prefixWord ++ tailWord_2968273).sum := by decide
  have hdescent : baseEnd_2968273 < baseStart_2968273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968274 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_2968274 : Nat := 118140960795 + 2968274 * 2 ^ 59
def prefixEnd_2968274 : Nat := 4983230072969 + 3 ^ 40 * 2968274 * 2
def baseEnd_2968274 : Nat := 508050425414608282674721

theorem tailTrace_2968274 : CollatzResearch.WordTrace tailWord_2968274 prefixEnd_2968274 508050425414608282674721 := by
  unfold tailWord_2968274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27065461712114428421171969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72174564565638475789791917 27065461712114428421171969)
  ·
    refine ⟨20299096284085821315878977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27065461712114428421171969 20299096284085821315878977)
    ·
      refine ⟨15224322213064365986909233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20299096284085821315878977 15224322213064365986909233)
      ·
        refine ⟨11418241659798274490181925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15224322213064365986909233 11418241659798274490181925)
        ·
          refine ⟨2140920311212176466909111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11418241659798274490181925 2140920311212176466909111)
          ·
            refine ⟨3211380466818264700363667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140920311212176466909111 3211380466818264700363667)
            ·
              refine ⟨4817070700227397050545501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211380466818264700363667 4817070700227397050545501)
              ·
                refine ⟨1806401512585273893954563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4817070700227397050545501 1806401512585273893954563)
                ·
                  refine ⟨2709602268877910840931845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806401512585273893954563 2709602268877910840931845)
                  ·
                    refine ⟨508050425414608282674721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709602268877910840931845 508050425414608282674721)
                    ·
                      rfl

theorem cell23_2968274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_2968274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968274 prefixEnd_2968274 := by exact prefixLift 2968274
  have htrace : WordTrace (prefixWord ++ tailWord_2968274) baseStart_2968274 baseEnd_2968274 := by
    simpa [prefixWord, tailWord_2968274, baseEnd_2968274] using wordTrace_append hprefix tailTrace_2968274
  have hstable : (prefixWord ++ tailWord_2968274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968274).length < 2 ^ (prefixWord ++ tailWord_2968274).sum := by decide
  have hdescent : baseEnd_2968274 < baseStart_2968274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968316 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2968316 : Nat := 118140960795 + 2968316 * 2 ^ 59
def prefixEnd_2968316 : Nat := 4983230072969 + 3 ^ 40 * 2968316 * 2
def baseEnd_2968316 : Nat := 1524172842431313683698969

theorem tailTrace_2968316 : CollatzResearch.WordTrace tailWord_2968316 prefixEnd_2968316 1524172842431313683698969 := by
  unfold tailWord_2968316
  simp only [CollatzResearch.WordTrace]
  refine ⟨54131689357152777428858401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72175585809537036571811201 54131689357152777428858401)
  ·
    refine ⟨40598767017864583071643801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54131689357152777428858401 40598767017864583071643801)
    ·
      refine ⟨30449075263398437303732851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40598767017864583071643801 30449075263398437303732851)
      ·
        refine ⟨45673612895097655955599277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30449075263398437303732851 45673612895097655955599277)
        ·
          refine ⟨17127604835661620983349729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45673612895097655955599277 17127604835661620983349729)
          ·
            refine ⟨12845703626746215737512297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17127604835661620983349729 12845703626746215737512297)
            ·
              refine ⟨9634277720059661803134223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12845703626746215737512297 9634277720059661803134223)
              ·
                refine ⟨14451416580089492704701335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634277720059661803134223 14451416580089492704701335)
                ·
                  refine ⟨21677124870134239057052003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14451416580089492704701335 21677124870134239057052003)
                  ·
                    refine ⟨32515687305201358585578005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21677124870134239057052003 32515687305201358585578005)
                    ·
                      refine ⟨1524172842431313683698969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32515687305201358585578005 1524172842431313683698969)
                      ·
                        rfl

theorem cell23_2968316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2968316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968316 prefixEnd_2968316 := by exact prefixLift 2968316
  have htrace : WordTrace (prefixWord ++ tailWord_2968316) baseStart_2968316 baseEnd_2968316 := by
    simpa [prefixWord, tailWord_2968316, baseEnd_2968316] using wordTrace_append hprefix tailTrace_2968316
  have hstable : (prefixWord ++ tailWord_2968316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968316).length < 2 ^ (prefixWord ++ tailWord_2968316).sum := by decide
  have hdescent : baseEnd_2968316 < baseStart_2968316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968354 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_2968354 : Nat := 118140960795 + 2968354 * 2 ^ 59
def prefixEnd_2968354 : Nat := 4983230072969 + 3 ^ 40 * 2968354 * 2
def baseEnd_2968354 : Nat := 1524192354696184535023795

theorem tailTrace_2968354 : CollatzResearch.WordTrace tailWord_2968354 prefixEnd_2968354 1524192354696184535023795 := by
  unfold tailWord_2968354
  simp only [CollatzResearch.WordTrace]
  refine ⟨27066191172041971836900029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72176509792111924898400077 27066191172041971836900029)
  ·
    refine ⟨10149821689515739438837511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27066191172041971836900029 10149821689515739438837511)
    ·
      refine ⟨15224732534273609158256267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10149821689515739438837511 15224732534273609158256267)
      ·
        refine ⟨22837098801410413737384401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15224732534273609158256267 22837098801410413737384401)
        ·
          refine ⟨17127824101057810303038301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22837098801410413737384401 17127824101057810303038301)
          ·
            refine ⟨6422934037896678863639363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17127824101057810303038301 6422934037896678863639363)
            ·
              refine ⟨9634401056845018295459045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422934037896678863639363 9634401056845018295459045)
              ·
                refine ⟨1806450198158440930398571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9634401056845018295459045 1806450198158440930398571)
                ·
                  refine ⟨2709675297237661395597857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806450198158440930398571 2709675297237661395597857)
                  ·
                    refine ⟨2032256472928246046698393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2709675297237661395597857 2032256472928246046698393)
                    ·
                      refine ⟨1524192354696184535023795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032256472928246046698393 1524192354696184535023795)
                      ·
                        rfl

theorem cell23_2968354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_2968354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968354 prefixEnd_2968354 := by exact prefixLift 2968354
  have htrace : WordTrace (prefixWord ++ tailWord_2968354) baseStart_2968354 baseEnd_2968354 := by
    simpa [prefixWord, tailWord_2968354, baseEnd_2968354] using wordTrace_append hprefix tailTrace_2968354
  have hstable : (prefixWord ++ tailWord_2968354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968354).length < 2 ^ (prefixWord ++ tailWord_2968354).sum := by decide
  have hdescent : baseEnd_2968354 < baseStart_2968354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968363 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 3, 3, 2]
def baseStart_2968363 : Nat := 118140960795 + 2968363 * 2 ^ 59
def prefixEnd_2968363 : Nat := 4983230072969 + 3 ^ 40 * 2968363 * 2
def baseEnd_2968363 : Nat := 1524196976022074999811253

theorem tailTrace_2968363 : CollatzResearch.WordTrace tailWord_2968363 prefixEnd_2968363 1524196976022074999811253 := by
  unfold tailWord_2968363
  simp only [CollatzResearch.WordTrace]
  refine ⟨108265092945135281884677743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72176728630090187923118495 108265092945135281884677743)
  ·
    refine ⟨162397639417702922827016615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108265092945135281884677743 162397639417702922827016615)
    ·
      refine ⟨243596459126554384240524923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162397639417702922827016615 243596459126554384240524923)
      ·
        refine ⟨365394688689831576360787385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243596459126554384240524923 365394688689831576360787385)
        ·
          refine ⟨274046016517373682270590539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365394688689831576360787385 274046016517373682270590539)
          ·
            refine ⟨411069024776060523405885809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274046016517373682270590539 411069024776060523405885809)
            ·
              refine ⟨308301768582045392554414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411069024776060523405885809 308301768582045392554414357)
              ·
                refine ⟨14451645402283377775988173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 308301768582045392554414357 14451645402283377775988173)
                ·
                  refine ⟨5419367025856266665995565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14451645402283377775988173 5419367025856266665995565)
                  ·
                    refine ⟨2032262634696099999748337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5419367025856266665995565 2032262634696099999748337)
                    ·
                      refine ⟨1524196976022074999811253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032262634696099999748337 1524196976022074999811253)
                      ·
                        rfl

theorem cell23_2968363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3, 2].length) (baseStart_2968363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968363 prefixEnd_2968363 := by exact prefixLift 2968363
  have htrace : WordTrace (prefixWord ++ tailWord_2968363) baseStart_2968363 baseEnd_2968363 := by
    simpa [prefixWord, tailWord_2968363, baseEnd_2968363] using wordTrace_append hprefix tailTrace_2968363
  have hstable : (prefixWord ++ tailWord_2968363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968363).length < 2 ^ (prefixWord ++ tailWord_2968363).sum := by decide
  have hdescent : baseEnd_2968363 < baseStart_2968363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968370 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_2968370 : Nat := 118140960795 + 2968370 * 2 ^ 59
def prefixEnd_2968370 : Nat := 4983230072969 + 3 ^ 40 * 2968370 * 2
def baseEnd_2968370 : Nat := 1524200570386656472423721

theorem tailTrace_2968370 : CollatzResearch.WordTrace tailWord_2968370 prefixEnd_2968370 1524200570386656472423721 := by
  unfold tailWord_2968370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27066337064027480520045641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72176898837406614720121709 27066337064027480520045641)
  ·
    refine ⟨20299752798020610390034231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27066337064027480520045641 20299752798020610390034231)
    ·
      refine ⟨30449629197030915585051347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20299752798020610390034231 30449629197030915585051347)
      ·
        refine ⟨45674443795546373377577021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30449629197030915585051347 45674443795546373377577021)
        ·
          refine ⟨17127916423329890016591383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45674443795546373377577021 17127916423329890016591383)
          ·
            refine ⟨25691874634994835024887075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17127916423329890016591383 25691874634994835024887075)
            ·
              refine ⟨38537811952492252537330613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25691874634994835024887075 38537811952492252537330613)
              ·
                refine ⟨3612919870546148675374745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38537811952492252537330613 3612919870546148675374745)
                ·
                  refine ⟨2709689902909611506531059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612919870546148675374745 2709689902909611506531059)
                  ·
                    refine ⟨4064534854364417259796589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2709689902909611506531059 4064534854364417259796589)
                    ·
                      refine ⟨1524200570386656472423721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064534854364417259796589 1524200570386656472423721)
                      ·
                        rfl

theorem cell23_2968370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_2968370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968370 prefixEnd_2968370 := by exact prefixLift 2968370
  have htrace : WordTrace (prefixWord ++ tailWord_2968370) baseStart_2968370 baseEnd_2968370 := by
    simpa [prefixWord, tailWord_2968370, baseEnd_2968370] using wordTrace_append hprefix tailTrace_2968370
  have hstable : (prefixWord ++ tailWord_2968370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968370).length < 2 ^ (prefixWord ++ tailWord_2968370).sum := by decide
  have hdescent : baseEnd_2968370 < baseStart_2968370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968376 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_2968376 : Nat := 118140960795 + 2968376 * 2 ^ 59
def prefixEnd_2968376 : Nat := 4983230072969 + 3 ^ 40 * 2968376 * 2
def baseEnd_2968376 : Nat := 1524203651270583448948693

theorem tailTrace_2968376 : CollatzResearch.WordTrace tailWord_2968376 prefixEnd_2968376 1524203651270583448948693 := by
  unfold tailWord_2968376
  simp only [CollatzResearch.WordTrace]
  refine ⟨54132783547044092552450491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72177044729392123403267321 54132783547044092552450491)
  ·
    refine ⟨81199175320566138828675737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54132783547044092552450491 81199175320566138828675737)
    ·
      refine ⟨60899381490424604121506803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81199175320566138828675737 60899381490424604121506803)
      ·
        refine ⟨91349072235636906182260205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60899381490424604121506803 91349072235636906182260205)
        ·
          refine ⟨34255902088363839818347577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91349072235636906182260205 34255902088363839818347577)
          ·
            refine ⟨25691926566272879863760683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34255902088363839818347577 25691926566272879863760683)
            ·
              refine ⟨38537889849409319795641025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25691926566272879863760683 38537889849409319795641025)
              ·
                refine ⟨28903417387056989846730769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38537889849409319795641025 28903417387056989846730769)
                ·
                  refine ⟨21677563040292742385048077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28903417387056989846730769 21677563040292742385048077)
                  ·
                    refine ⟨8129086140109778394393029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21677563040292742385048077 8129086140109778394393029)
                    ·
                      refine ⟨1524203651270583448948693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8129086140109778394393029 1524203651270583448948693)
                      ·
                        rfl

theorem cell23_2968376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_2968376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968376 prefixEnd_2968376 := by exact prefixLift 2968376
  have htrace : WordTrace (prefixWord ++ tailWord_2968376) baseStart_2968376 baseEnd_2968376 := by
    simpa [prefixWord, tailWord_2968376, baseEnd_2968376] using wordTrace_append hprefix tailTrace_2968376
  have hstable : (prefixWord ++ tailWord_2968376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968376).length < 2 ^ (prefixWord ++ tailWord_2968376).sum := by decide
  have hdescent : baseEnd_2968376 < baseStart_2968376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968380 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_2968380 : Nat := 118140960795 + 2968380 * 2 ^ 59
def prefixEnd_2968380 : Nat := 4983230072969 + 3 ^ 40 * 2968380 * 2
def baseEnd_2968380 : Nat := 1524205705193201433298675

theorem tailTrace_2968380 : CollatzResearch.WordTrace tailWord_2968380 prefixEnd_2968380 1524205705193201433298675 := by
  unfold tailWord_2968380
  simp only [CollatzResearch.WordTrace]
  refine ⟨54132856493036846894023297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72177141990715795858697729 54132856493036846894023297)
  ·
    refine ⟨40599642369777635170517473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54132856493036846894023297 40599642369777635170517473)
    ·
      refine ⟨30449731777333226377888105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40599642369777635170517473 30449731777333226377888105)
      ·
        refine ⟨22837298832999919783416079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30449731777333226377888105 22837298832999919783416079)
        ·
          refine ⟨34255948249499879675124119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22837298832999919783416079 34255948249499879675124119)
          ·
            refine ⟨51383922374249819512686179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34255948249499879675124119 51383922374249819512686179)
            ·
              refine ⟨77075883561374729269029269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51383922374249819512686179 77075883561374729269029269)
              ·
                refine ⟨3612932041939440434485747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77075883561374729269029269 3612932041939440434485747)
                ·
                  refine ⟨5419398062909160651728621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612932041939440434485747 5419398062909160651728621)
                  ·
                    refine ⟨2032274273590935244398233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5419398062909160651728621 2032274273590935244398233)
                    ·
                      refine ⟨1524205705193201433298675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032274273590935244398233 1524205705193201433298675)
                      ·
                        rfl

theorem cell23_2968380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_2968380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968380 prefixEnd_2968380 := by exact prefixLift 2968380
  have htrace : WordTrace (prefixWord ++ tailWord_2968380) baseStart_2968380 baseEnd_2968380 := by
    simpa [prefixWord, tailWord_2968380, baseEnd_2968380] using wordTrace_append hprefix tailTrace_2968380
  have hstable : (prefixWord ++ tailWord_2968380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968380).length < 2 ^ (prefixWord ++ tailWord_2968380).sum := by decide
  have hdescent : baseEnd_2968380 < baseStart_2968380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968388 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2968388 : Nat := 118140960795 + 2968388 * 2 ^ 59
def prefixEnd_2968388 : Nat := 4983230072969 + 3 ^ 40 * 2968388 * 2
def baseEnd_2968388 : Nat := 1524209813038437401998639

theorem tailTrace_2968388 : CollatzResearch.WordTrace tailWord_2968388 prefixEnd_2968388 1524209813038437401998639 := by
  unfold tailWord_2968388
  simp only [CollatzResearch.WordTrace]
  refine ⟨54133002385022355577168909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72177336513363140769558545 54133002385022355577168909)
  ·
    refine ⟨20299875894383383341438341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54133002385022355577168909 20299875894383383341438341)
    ·
      refine ⟨3806226730196884376519689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20299875894383383341438341 3806226730196884376519689)
      ·
        refine ⟨2854670047647663282389767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3806226730196884376519689 2854670047647663282389767)
        ·
          refine ⟨4282005071471494923584651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854670047647663282389767 4282005071471494923584651)
          ·
            refine ⟨6423007607207242385376977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4282005071471494923584651 6423007607207242385376977)
            ·
              refine ⟨4817255705405431789032733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423007607207242385376977 4817255705405431789032733)
              ·
                refine ⟨1806470889527036920887275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4817255705405431789032733 1806470889527036920887275)
                ·
                  refine ⟨2709706334290555381330913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806470889527036920887275 2709706334290555381330913)
                  ·
                    refine ⟨2032279750717916535998185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2709706334290555381330913 2032279750717916535998185)
                    ·
                      refine ⟨1524209813038437401998639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032279750717916535998185 1524209813038437401998639)
                      ·
                        rfl

theorem cell23_2968388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2968388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968388 prefixEnd_2968388 := by exact prefixLift 2968388
  have htrace : WordTrace (prefixWord ++ tailWord_2968388) baseStart_2968388 baseEnd_2968388 := by
    simpa [prefixWord, tailWord_2968388, baseEnd_2968388] using wordTrace_append hprefix tailTrace_2968388
  have hstable : (prefixWord ++ tailWord_2968388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968388).length < 2 ^ (prefixWord ++ tailWord_2968388).sum := by decide
  have hdescent : baseEnd_2968388 < baseStart_2968388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968404 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2968404 : Nat := 118140960795 + 2968404 * 2 ^ 59
def prefixEnd_2968404 : Nat := 4983230072969 + 3 ^ 40 * 2968404 * 2
def baseEnd_2968404 : Nat := 1524218028728909339398565

theorem tailTrace_2968404 : CollatzResearch.WordTrace tailWord_2968404 prefixEnd_2968404 1524218028728909339398565 := by
  unfold tailWord_2968404
  simp only [CollatzResearch.WordTrace]
  refine ⟨54133294168993372943460133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72177725558657830591280177 54133294168993372943460133)
  ·
    refine ⟨10149992656686257426898775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54133294168993372943460133 10149992656686257426898775)
    ·
      refine ⟨15224988985029386140348163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10149992656686257426898775 15224988985029386140348163)
      ·
        refine ⟨22837483477544079210522245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15224988985029386140348163 22837483477544079210522245)
        ·
          refine ⟨4282028152039514851972921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22837483477544079210522245 4282028152039514851972921)
          ·
            refine ⟨3211521114029636138979691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282028152039514851972921 3211521114029636138979691)
            ·
              refine ⟨4817281671044454208469537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211521114029636138979691 4817281671044454208469537)
              ·
                refine ⟨3612961253283340656352153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817281671044454208469537 3612961253283340656352153)
                ·
                  refine ⟨2709720939962505492264115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612961253283340656352153 2709720939962505492264115)
                  ·
                    refine ⟨4064581409943758238396173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2709720939962505492264115 4064581409943758238396173)
                    ·
                      refine ⟨1524218028728909339398565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064581409943758238396173 1524218028728909339398565)
                      ·
                        rfl

theorem cell23_2968404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2968404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968404 prefixEnd_2968404 := by exact prefixLift 2968404
  have htrace : WordTrace (prefixWord ++ tailWord_2968404) baseStart_2968404 baseEnd_2968404 := by
    simpa [prefixWord, tailWord_2968404, baseEnd_2968404] using wordTrace_append hprefix tailTrace_2968404
  have hstable : (prefixWord ++ tailWord_2968404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968404).length < 2 ^ (prefixWord ++ tailWord_2968404).sum := by decide
  have hdescent : baseEnd_2968404 < baseStart_2968404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968423 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2968423 : Nat := 118140960795 + 2968423 * 2 ^ 59
def prefixEnd_2968423 : Nat := 4983230072969 + 3 ^ 40 * 2968423 * 2
def baseEnd_2968423 : Nat := 1524227784861344765060977

theorem tailTrace_2968423 : CollatzResearch.WordTrace tailWord_2968423 prefixEnd_2968423 1524227784861344765060977 := by
  unfold tailWord_2968423
  simp only [CollatzResearch.WordTrace]
  refine ⟨108267281324917912131861923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72178187549945274754574615 108267281324917912131861923)
  ·
    refine ⟨162400921987376868197792885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108267281324917912131861923 162400921987376868197792885)
    ·
      refine ⟨15225086436316581393543083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162400921987376868197792885 15225086436316581393543083)
      ·
        refine ⟨22837629654474872090314625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15225086436316581393543083 22837629654474872090314625)
        ·
          refine ⟨17128222240856154067735969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22837629654474872090314625 17128222240856154067735969)
          ·
            refine ⟨12846166680642115550801977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17128222240856154067735969 12846166680642115550801977)
            ·
              refine ⟨9634625010481586663101483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12846166680642115550801977 9634625010481586663101483)
              ·
                refine ⟨14451937515722379994652225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634625010481586663101483 14451937515722379994652225)
                ·
                  refine ⟨10838953136791784995989169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14451937515722379994652225 10838953136791784995989169)
                  ·
                    refine ⟨8129214852593838746991877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10838953136791784995989169 8129214852593838746991877)
                    ·
                      refine ⟨1524227784861344765060977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8129214852593838746991877 1524227784861344765060977)
                      ·
                        rfl

theorem cell23_2968423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2968423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968423 prefixEnd_2968423 := by exact prefixLift 2968423
  have htrace : WordTrace (prefixWord ++ tailWord_2968423) baseStart_2968423 baseEnd_2968423 := by
    simpa [prefixWord, tailWord_2968423, baseEnd_2968423] using wordTrace_append hprefix tailTrace_2968423
  have hstable : (prefixWord ++ tailWord_2968423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968423).length < 2 ^ (prefixWord ++ tailWord_2968423).sum := by decide
  have hdescent : baseEnd_2968423 < baseStart_2968423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968503 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_2968503 : Nat := 118140960795 + 2968503 * 2 ^ 59
def prefixEnd_2968503 : Nat := 4983230072969 + 3 ^ 40 * 2968503 * 2
def baseEnd_2968503 : Nat := 1524268863313704452060609

theorem tailTrace_2968503 : CollatzResearch.WordTrace tailWord_2968503 prefixEnd_2968503 1524268863313704452060609 := by
  unfold tailWord_2968503
  simp only [CollatzResearch.WordTrace]
  refine ⟨108270199164628085794774163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72180132776418723863182775 108270199164628085794774163)
  ·
    refine ⟨162405298746942128692161245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108270199164628085794774163 162405298746942128692161245)
    ·
      refine ⟨60901987030103298259560467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162405298746942128692161245 60901987030103298259560467)
      ·
        refine ⟨91352980545154947389340701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60901987030103298259560467 91352980545154947389340701)
        ·
          refine ⟨34257367704433105271002763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91352980545154947389340701 34257367704433105271002763)
          ·
            refine ⟨51386051556649657906504145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34257367704433105271002763 51386051556649657906504145)
            ·
              refine ⟨38539538667487243429878109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51386051556649657906504145 38539538667487243429878109)
              ·
                refine ⟨14452327000307716286204291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38539538667487243429878109 14452327000307716286204291)
                ·
                  refine ⟨21678490500461574429306437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14452327000307716286204291 21678490500461574429306437)
                  ·
                    refine ⟨4064716968836545205494957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21678490500461574429306437 4064716968836545205494957)
                    ·
                      refine ⟨1524268863313704452060609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064716968836545205494957 1524268863313704452060609)
                      ·
                        rfl

theorem cell23_2968503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_2968503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968503 prefixEnd_2968503 := by exact prefixLift 2968503
  have htrace : WordTrace (prefixWord ++ tailWord_2968503) baseStart_2968503 baseEnd_2968503 := by
    simpa [prefixWord, tailWord_2968503, baseEnd_2968503] using wordTrace_append hprefix tailTrace_2968503
  have hstable : (prefixWord ++ tailWord_2968503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968503).length < 2 ^ (prefixWord ++ tailWord_2968503).sum := by decide
  have hdescent : baseEnd_2968503 < baseStart_2968503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968518 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_2968518 : Nat := 118140960795 + 2968518 * 2 ^ 59
def prefixEnd_2968518 : Nat := 4983230072969 + 3 ^ 40 * 2968518 * 2
def baseEnd_2968518 : Nat := 169364062835946877041449

theorem tailTrace_2968518 : CollatzResearch.WordTrace tailWord_2968518 prefixEnd_2968518 169364062835946877041449 := by
  unfold tailWord_2968518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383460820611679479892819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72180497506382495571046805 3383460820611679479892819)
  ·
    refine ⟨5075191230917519219839229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383460820611679479892819 5075191230917519219839229)
    ·
      refine ⟨1903196711594069707439711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5075191230917519219839229 1903196711594069707439711)
      ·
        refine ⟨2854795067391104561159567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1903196711594069707439711 2854795067391104561159567)
        ·
          refine ⟨4282192601086656841739351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854795067391104561159567 4282192601086656841739351)
          ·
            refine ⟨6423288901629985262609027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4282192601086656841739351 6423288901629985262609027)
            ·
              refine ⟨9634933352444977893913541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423288901629985262609027 9634933352444977893913541)
              ·
                refine ⟨1806550003583433355108789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9634933352444977893913541 1806550003583433355108789)
                ·
                  refine ⟨169364062835946877041449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806550003583433355108789 169364062835946877041449)
                  ·
                    rfl

theorem cell23_2968518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_2968518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968518 prefixEnd_2968518 := by exact prefixLift 2968518
  have htrace : WordTrace (prefixWord ++ tailWord_2968518) baseStart_2968518 baseEnd_2968518 := by
    simpa [prefixWord, tailWord_2968518, baseEnd_2968518] using wordTrace_append hprefix tailTrace_2968518
  have hstable : (prefixWord ++ tailWord_2968518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968518).length < 2 ^ (prefixWord ++ tailWord_2968518).sum := by decide
  have hdescent : baseEnd_2968518 < baseStart_2968518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968523 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 6]
def baseStart_2968523 : Nat := 118140960795 + 2968523 * 2 ^ 59
def prefixEnd_2968523 : Nat := 4983230072969 + 3 ^ 40 * 2968523 * 2
def baseEnd_2968523 : Nat := 169364348102977152645613

theorem tailTrace_2968523 : CollatzResearch.WordTrace tailWord_2968523 prefixEnd_2968523 169364348102977152645613 := by
  unfold tailWord_2968523
  simp only [CollatzResearch.WordTrace]
  refine ⟨108270928624555629210502223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72180619083037086140334815 108270928624555629210502223)
  ·
    refine ⟨162406392936833443815753335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108270928624555629210502223 162406392936833443815753335)
    ·
      refine ⟨243609589405250165723630003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162406392936833443815753335 243609589405250165723630003)
      ·
        refine ⟨365414384107875248585445005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243609589405250165723630003 365414384107875248585445005)
        ·
          refine ⟨137030394040453218219541877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365414384107875248585445005 137030394040453218219541877)
          ·
            refine ⟨12846599441292489208082051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137030394040453218219541877 12846599441292489208082051)
            ·
              refine ⟨19269899161938733812123077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12846599441292489208082051 19269899161938733812123077)
              ·
                refine ⟨3613106092863512589773077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19269899161938733812123077 3613106092863512589773077)
                ·
                  refine ⟨169364348102977152645613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3613106092863512589773077 169364348102977152645613)
                  ·
                    rfl

theorem cell23_2968523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 6].length) (baseStart_2968523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968523 prefixEnd_2968523 := by exact prefixLift 2968523
  have htrace : WordTrace (prefixWord ++ tailWord_2968523) baseStart_2968523 baseEnd_2968523 := by
    simpa [prefixWord, tailWord_2968523, baseEnd_2968523] using wordTrace_append hprefix tailTrace_2968523
  have hstable : (prefixWord ++ tailWord_2968523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968523).length < 2 ^ (prefixWord ++ tailWord_2968523).sum := by decide
  have hdescent : baseEnd_2968523 < baseStart_2968523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968527 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 1, 4]
def baseStart_2968527 : Nat := 118140960795 + 2968527 * 2 ^ 59
def prefixEnd_2968527 : Nat := 4983230072969 + 3 ^ 40 * 2968527 * 2
def baseEnd_2968527 : Nat := 508093728949804119386833

theorem tailTrace_2968527 : CollatzResearch.WordTrace tailWord_2968527 prefixEnd_2968527 508093728949804119386833 := by
  unfold tailWord_2968527
  simp only [CollatzResearch.WordTrace]
  refine ⟨108271074516541137893647835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72180716344360758595765223 108271074516541137893647835)
  ·
    refine ⟨162406611774811706840471753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108271074516541137893647835 162406611774811706840471753)
    ·
      refine ⟨121804958831108780130353815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162406611774811706840471753 121804958831108780130353815)
      ·
        refine ⟨182707438246663170195530723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121804958831108780130353815 182707438246663170195530723)
        ·
          refine ⟨274061157369994755293296085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182707438246663170195530723 274061157369994755293296085)
          ·
            refine ⟨6423308375859252077186627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 274061157369994755293296085 6423308375859252077186627)
            ·
              refine ⟨9634962563788878115779941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423308375859252077186627 9634962563788878115779941)
              ·
                refine ⟨1806555480710414646708739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9634962563788878115779941 1806555480710414646708739)
                ·
                  refine ⟨2709833221065621970063109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806555480710414646708739 2709833221065621970063109)
                  ·
                    refine ⟨508093728949804119386833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709833221065621970063109 508093728949804119386833)
                    ·
                      rfl

theorem cell23_2968527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 4].length) (baseStart_2968527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968527 prefixEnd_2968527 := by exact prefixLift 2968527
  have htrace : WordTrace (prefixWord ++ tailWord_2968527) baseStart_2968527 baseEnd_2968527 := by
    simpa [prefixWord, tailWord_2968527, baseEnd_2968527] using wordTrace_append hprefix tailTrace_2968527
  have hstable : (prefixWord ++ tailWord_2968527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968527).length < 2 ^ (prefixWord ++ tailWord_2968527).sum := by decide
  have hdescent : baseEnd_2968527 < baseStart_2968527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968534 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_2968534 : Nat := 118140960795 + 2968534 * 2 ^ 59
def prefixEnd_2968534 : Nat := 4983230072969 + 3 ^ 40 * 2968534 * 2
def baseEnd_2968534 : Nat := 1524284781213993830772967

theorem tailTrace_2968534 : CollatzResearch.WordTrace tailWord_2968534 prefixEnd_2968534 1524284781213993830772967 := by
  unfold tailWord_2968534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766958114219736130572041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72180886551677185392768437 6766958114219736130572041)
  ·
    refine ⟨5075218585664802097929031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6766958114219736130572041 5075218585664802097929031)
    ·
      refine ⟨7612827878497203146893547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5075218585664802097929031 7612827878497203146893547)
      ·
        refine ⟨11419241817745804720340321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7612827878497203146893547 11419241817745804720340321)
        ·
          refine ⟨8564431363309353540255241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11419241817745804720340321 8564431363309353540255241)
          ·
            refine ⟨6423323522482015155191431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8564431363309353540255241 6423323522482015155191431)
            ·
              refine ⟨9634985283723022732787147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423323522482015155191431 9634985283723022732787147)
              ·
                refine ⟨14452477925584534099180721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634985283723022732787147 14452477925584534099180721)
                ·
                  refine ⟨10839358444188400574385541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14452477925584534099180721 10839358444188400574385541)
                  ·
                    refine ⟨2032379708285325107697289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10839358444188400574385541 2032379708285325107697289)
                    ·
                      refine ⟨1524284781213993830772967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032379708285325107697289 1524284781213993830772967)
                      ·
                        rfl

theorem cell23_2968534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_2968534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968534 prefixEnd_2968534 := by exact prefixLift 2968534
  have htrace : WordTrace (prefixWord ++ tailWord_2968534) baseStart_2968534 baseEnd_2968534 := by
    simpa [prefixWord, tailWord_2968534, baseEnd_2968534] using wordTrace_append hprefix tailTrace_2968534
  have hstable : (prefixWord ++ tailWord_2968534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968534).length < 2 ^ (prefixWord ++ tailWord_2968534).sum := by decide
  have hdescent : baseEnd_2968534 < baseStart_2968534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968574 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_2968574 : Nat := 118140960795 + 2968574 * 2 ^ 59
def prefixEnd_2968574 : Nat := 4983230072969 + 3 ^ 40 * 2968574 * 2
def baseEnd_2968574 : Nat := 169367257826685963808087

theorem tailTrace_2968574 : CollatzResearch.WordTrace tailWord_2968574 prefixEnd_2968574 169367257826685963808087 := by
  unfold tailWord_2968574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13534098593421358115076097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72181859164913909947072517 13534098593421358115076097)
  ·
    refine ⟨10150573945066018586307073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13534098593421358115076097 10150573945066018586307073)
    ·
      refine ⟨7612930458799513939730305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10150573945066018586307073 7612930458799513939730305)
      ·
        refine ⟨5709697844099635454797729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7612930458799513939730305 5709697844099635454797729)
        ·
          refine ⟨4282273383074726591098297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5709697844099635454797729 4282273383074726591098297)
          ·
            refine ⟨3211705037306044943323723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282273383074726591098297 3211705037306044943323723)
            ·
              refine ⟨4817557555959067414985585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211705037306044943323723 4817557555959067414985585)
              ·
                refine ⟨3613168166969300561239189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817557555959067414985585 3613168166969300561239189)
                ·
                  refine ⟨169367257826685963808087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3613168166969300561239189 169367257826685963808087)
                  ·
                    rfl

theorem cell23_2968574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_2968574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968574 prefixEnd_2968574 := by exact prefixLift 2968574
  have htrace : WordTrace (prefixWord ++ tailWord_2968574) baseStart_2968574 baseEnd_2968574 := by
    simpa [prefixWord, tailWord_2968574, baseEnd_2968574] using wordTrace_append hprefix tailTrace_2968574
  have hstable : (prefixWord ++ tailWord_2968574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968574).length < 2 ^ (prefixWord ++ tailWord_2968574).sum := by decide
  have hdescent : baseEnd_2968574 < baseStart_2968574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968584 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_2968584 : Nat := 118140960795 + 2968584 * 2 ^ 59
def prefixEnd_2968584 : Nat := 4983230072969 + 3 ^ 40 * 2968584 * 2
def baseEnd_2968584 : Nat := 1524310455246718635147737

theorem tailTrace_2968584 : CollatzResearch.WordTrace tailWord_2968584 prefixEnd_2968584 1524310455246718635147737 := by
  unfold tailWord_2968584
  simp only [CollatzResearch.WordTrace]
  refine ⟨54136576738667318314236403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72182102318223091085648537 54136576738667318314236403)
  ·
    refine ⟨81204865108000977471354605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54136576738667318314236403 81204865108000977471354605)
    ·
      refine ⟨30451824415500366551757977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81204865108000977471354605 30451824415500366551757977)
      ·
        refine ⟨22838868311625274913818483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30451824415500366551757977 22838868311625274913818483)
        ·
          refine ⟨34258302467437912370727725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22838868311625274913818483 34258302467437912370727725)
          ·
            refine ⟨12846863425289217139022897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34258302467437912370727725 12846863425289217139022897)
            ·
              refine ⟨9635147568966912854267173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12846863425289217139022897 9635147568966912854267173)
              ·
                refine ⟨1806590169181296160175095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9635147568966912854267173 1806590169181296160175095)
                ·
                  refine ⟨2709885253771944240262643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806590169181296160175095 2709885253771944240262643)
                  ·
                    refine ⟨4064827880657916360393965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2709885253771944240262643 4064827880657916360393965)
                    ·
                      refine ⟨1524310455246718635147737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064827880657916360393965 1524310455246718635147737)
                      ·
                        rfl

theorem cell23_2968584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_2968584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968584 prefixEnd_2968584 := by exact prefixLift 2968584
  have htrace : WordTrace (prefixWord ++ tailWord_2968584) baseStart_2968584 baseEnd_2968584 := by
    simpa [prefixWord, tailWord_2968584, baseEnd_2968584] using wordTrace_append hprefix tailTrace_2968584
  have hstable : (prefixWord ++ tailWord_2968584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968584).length < 2 ^ (prefixWord ++ tailWord_2968584).sum := by decide
  have hdescent : baseEnd_2968584 < baseStart_2968584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968600 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 1, 6]
def baseStart_2968600 : Nat := 118140960795 + 2968600 * 2 ^ 59
def prefixEnd_2968600 : Nat := 4983230072969 + 3 ^ 40 * 2968600 * 2
def baseEnd_2968600 : Nat := 508106223645730190849221

theorem tailTrace_2968600 : CollatzResearch.WordTrace tailWord_2968600 prefixEnd_2968600 508106223645730190849221 := by
  unfold tailWord_2968600
  simp only [CollatzResearch.WordTrace]
  refine ⟨54136868522638335680527627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72182491363517780907370169 54136868522638335680527627)
  ·
    refine ⟨81205302783957503520791441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54136868522638335680527627 81205302783957503520791441)
    ·
      refine ⟨60903977087968127640593581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81205302783957503520791441 60903977087968127640593581)
      ·
        refine ⟨22838991407988047865222593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60903977087968127640593581 22838991407988047865222593)
        ·
          refine ⟨17129243555991035898916945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22838991407988047865222593 17129243555991035898916945)
          ·
            refine ⟨12846932666993276924187709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17129243555991035898916945 12846932666993276924187709)
            ·
              refine ⟨4817599750122478846570391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12846932666993276924187709 4817599750122478846570391)
              ·
                refine ⟨7226399625183718269855587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817599750122478846570391 7226399625183718269855587)
                ·
                  refine ⟨10839599437775577404783381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226399625183718269855587 10839599437775577404783381)
                  ·
                    refine ⟨508106223645730190849221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10839599437775577404783381 508106223645730190849221)
                    ·
                      rfl

theorem cell23_2968600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_2968600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968600 prefixEnd_2968600 := by exact prefixLift 2968600
  have htrace : WordTrace (prefixWord ++ tailWord_2968600) baseStart_2968600 baseEnd_2968600 := by
    simpa [prefixWord, tailWord_2968600, baseEnd_2968600] using wordTrace_append hprefix tailTrace_2968600
  have hstable : (prefixWord ++ tailWord_2968600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968600).length < 2 ^ (prefixWord ++ tailWord_2968600).sum := by decide
  have hdescent : baseEnd_2968600 < baseStart_2968600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968607 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 4]
def baseStart_2968607 : Nat := 118140960795 + 2968607 * 2 ^ 59
def prefixEnd_2968607 : Nat := 4983230072969 + 3 ^ 40 * 2968607 * 2
def baseEnd_2968607 : Nat := 1524322265301772045160131

theorem tailTrace_2968607 : CollatzResearch.WordTrace tailWord_2968607 prefixEnd_2968607 1524322265301772045160131 := by
  unfold tailWord_2968607
  simp only [CollatzResearch.WordTrace]
  refine ⟨108273992356251311556560075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72182661570834207704373383 108273992356251311556560075)
  ·
    refine ⟨162410988534376967334840113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108273992356251311556560075 162410988534376967334840113)
    ·
      refine ⟨121808241400782725501130085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162410988534376967334840113 121808241400782725501130085)
      ·
        refine ⟨22839045262646761031461891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121808241400782725501130085 22839045262646761031461891)
        ·
          refine ⟨34258567893970141547192837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22839045262646761031461891 34258567893970141547192837)
          ·
            refine ⟨6423481480119401540098657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34258567893970141547192837 6423481480119401540098657)
            ·
              refine ⟨4817611110089551155073993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423481480119401540098657 4817611110089551155073993)
              ·
                refine ⟨3613208332567163366305495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817611110089551155073993 3613208332567163366305495)
                ·
                  refine ⟨5419812498850745049458243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613208332567163366305495 5419812498850745049458243)
                  ·
                    refine ⟨8129718748276117574187365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5419812498850745049458243 8129718748276117574187365)
                    ·
                      refine ⟨1524322265301772045160131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8129718748276117574187365 1524322265301772045160131)
                      ·
                        rfl

theorem cell23_2968607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_2968607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968607 prefixEnd_2968607 := by exact prefixLift 2968607
  have htrace : WordTrace (prefixWord ++ tailWord_2968607) baseStart_2968607 baseEnd_2968607 := by
    simpa [prefixWord, tailWord_2968607, baseEnd_2968607] using wordTrace_append hprefix tailTrace_2968607
  have hstable : (prefixWord ++ tailWord_2968607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968607).length < 2 ^ (prefixWord ++ tailWord_2968607).sum := by decide
  have hdescent : baseEnd_2968607 < baseStart_2968607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968613 : List Nat := [1, 3, 1, 2, 2, 2, 3, 9]
def baseStart_2968613 : Nat := 118140960795 + 2968613 * 2 ^ 59
def prefixEnd_2968613 : Nat := 4983230072969 + 3 ^ 40 * 2968613 * 2
def baseEnd_2968613 : Nat := 56456494303174037840189

theorem tailTrace_2968613 : CollatzResearch.WordTrace tailWord_2968613 prefixEnd_2968613 56456494303174037840189 := by
  unfold tailWord_2968613
  simp only [CollatzResearch.WordTrace]
  refine ⟨108274211194229574581278493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72182807462819716387518995 108274211194229574581278493)
  ·
    refine ⟨40602829197836090467979435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108274211194229574581278493 40602829197836090467979435)
    ·
      refine ⟨60904243796754135701969153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40602829197836090467979435 60904243796754135701969153)
      ·
        refine ⟨45678182847565601776476865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60904243796754135701969153 45678182847565601776476865)
        ·
          refine ⟨34258637135674201332357649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45678182847565601776476865 34258637135674201332357649)
          ·
            refine ⟨25693977851755650999268237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34258637135674201332357649 25693977851755650999268237)
            ·
              refine ⟨9635241694408369124725589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25693977851755650999268237 9635241694408369124725589)
              ·
                refine ⟨56456494303174037840189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9635241694408369124725589 56456494303174037840189)
                ·
                  rfl

theorem cell23_2968613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 9].length) (baseStart_2968613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968613 prefixEnd_2968613 := by exact prefixLift 2968613
  have htrace : WordTrace (prefixWord ++ tailWord_2968613) baseStart_2968613 baseEnd_2968613 := by
    simpa [prefixWord, tailWord_2968613, baseEnd_2968613] using wordTrace_append hprefix tailTrace_2968613
  have hstable : (prefixWord ++ tailWord_2968613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968613).length < 2 ^ (prefixWord ++ tailWord_2968613).sum := by decide
  have hdescent : baseEnd_2968613 < baseStart_2968613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968618 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2968618 : Nat := 118140960795 + 2968618 * 2 ^ 59
def prefixEnd_2968618 : Nat := 4983230072969 + 3 ^ 40 * 2968618 * 2
def baseEnd_2968618 : Nat := 1524327913588971502122581

theorem tailTrace_2968618 : CollatzResearch.WordTrace tailWord_2968618 prefixEnd_2968618 1524327913588971502122581 := by
  unfold tailWord_2968618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068598389802865108802627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72182929039474306956807005 27068598389802865108802627)
  ·
    refine ⟨40602897584704297663203941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27068598389802865108802627 40602897584704297663203941)
    ·
      refine ⟨7613043297132055811850739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40602897584704297663203941 7613043297132055811850739)
      ·
        refine ⟨11419564945698083717776109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613043297132055811850739 11419564945698083717776109)
        ·
          refine ⟨4282336854636781394166041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11419564945698083717776109 4282336854636781394166041)
          ·
            refine ⟨3211752640977586045624531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282336854636781394166041 3211752640977586045624531)
            ·
              refine ⟨4817628961466379068436797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211752640977586045624531 4817628961466379068436797)
              ·
                refine ⟨1806610860549892150663799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4817628961466379068436797 1806610860549892150663799)
                ·
                  refine ⟨2709916290824838225995699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806610860549892150663799 2709916290824838225995699)
                  ·
                    refine ⟨4064874436237257338993549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2709916290824838225995699 4064874436237257338993549)
                    ·
                      refine ⟨1524327913588971502122581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064874436237257338993549 1524327913588971502122581)
                      ·
                        rfl

theorem cell23_2968618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2968618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968618 prefixEnd_2968618 := by exact prefixLift 2968618
  have htrace : WordTrace (prefixWord ++ tailWord_2968618) baseStart_2968618 baseEnd_2968618 := by
    simpa [prefixWord, tailWord_2968618, baseEnd_2968618] using wordTrace_append hprefix tailTrace_2968618
  have hstable : (prefixWord ++ tailWord_2968618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968618).length < 2 ^ (prefixWord ++ tailWord_2968618).sum := by decide
  have hdescent : baseEnd_2968618 < baseStart_2968618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968630 : List Nat := [5, 1, 2, 1, 1, 2, 11]
def baseStart_2968630 : Nat := 118140960795 + 2968630 * 2 ^ 59
def prefixEnd_2968630 : Nat := 4983230072969 + 3 ^ 40 * 2968630 * 2
def baseEnd_2968630 : Nat := 18818939201936116730525

theorem tailTrace_2968630 : CollatzResearch.WordTrace tailWord_2968630 prefixEnd_2968630 18818939201936116730525 := by
  unfold tailWord_2968630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6767176952197999155290459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72183220823445324323098229 6767176952197999155290459)
  ·
    refine ⟨10150765428296998732935689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6767176952197999155290459 10150765428296998732935689)
    ·
      refine ⟨7613074071222749049701767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10150765428296998732935689 7613074071222749049701767)
      ·
        refine ⟨11419611106834123574552651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613074071222749049701767 11419611106834123574552651)
        ·
          refine ⟨17129416660251185361828977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11419611106834123574552651 17129416660251185361828977)
          ·
            refine ⟨12847062495188389021371733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17129416660251185361828977 12847062495188389021371733)
            ·
              refine ⟨18818939201936116730525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12847062495188389021371733 18818939201936116730525)
              ·
                rfl

theorem cell23_2968630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 11].length) (baseStart_2968630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968630 prefixEnd_2968630 := by exact prefixLift 2968630
  have htrace : WordTrace (prefixWord ++ tailWord_2968630) baseStart_2968630 baseEnd_2968630 := by
    simpa [prefixWord, tailWord_2968630, baseEnd_2968630] using wordTrace_append hprefix tailTrace_2968630
  have hstable : (prefixWord ++ tailWord_2968630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968630).length < 2 ^ (prefixWord ++ tailWord_2968630).sum := by decide
  have hdescent : baseEnd_2968630 < baseStart_2968630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968643 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 2, 7]
def baseStart_2968643 : Nat := 118140960795 + 2968643 * 2 ^ 59
def prefixEnd_2968643 : Nat := 4983230072969 + 3 ^ 40 * 2968643 * 2
def baseEnd_2968643 : Nat := 508113583535111301436655

theorem tailTrace_2968643 : CollatzResearch.WordTrace tailWord_2968643 prefixEnd_2968643 508113583535111301436655 := by
  unfold tailWord_2968643
  simp only [CollatzResearch.WordTrace]
  refine ⟨108275305384120889704870583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72183536922747259803247055 108275305384120889704870583)
  ·
    refine ⟨162412958076181334557305875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108275305384120889704870583 162412958076181334557305875)
    ·
      refine ⟨243619437114272001835958813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162412958076181334557305875 243619437114272001835958813)
      ·
        refine ⟨91357288917852000688484555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243619437114272001835958813 91357288917852000688484555)
        ·
          refine ⟨137035933376778001032726833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91357288917852000688484555 137035933376778001032726833)
          ·
            refine ⟨102776950032583500774545125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137035933376778001032726833 102776950032583500774545125)
            ·
              refine ⟨19270678131109406395227211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102776950032583500774545125 19270678131109406395227211)
              ·
                refine ⟨28906017196664109592840817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19270678131109406395227211 28906017196664109592840817)
                ·
                  refine ⟨21679512897498082194630613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28906017196664109592840817 21679512897498082194630613)
                  ·
                    refine ⟨508113583535111301436655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21679512897498082194630613 508113583535111301436655)
                    ·
                      rfl

theorem cell23_2968643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_2968643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968643 prefixEnd_2968643 := by exact prefixLift 2968643
  have htrace : WordTrace (prefixWord ++ tailWord_2968643) baseStart_2968643 baseEnd_2968643 := by
    simpa [prefixWord, tailWord_2968643, baseEnd_2968643] using wordTrace_append hprefix tailTrace_2968643
  have hstable : (prefixWord ++ tailWord_2968643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968643).length < 2 ^ (prefixWord ++ tailWord_2968643).sum := by decide
  have hdescent : baseEnd_2968643 < baseStart_2968643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968663 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2968663 : Nat := 118140960795 + 2968663 * 2 ^ 59
def prefixEnd_2968663 : Nat := 4983230072969 + 3 ^ 40 * 2968663 * 2
def baseEnd_2968663 : Nat := 1524351020218423826059873

theorem tailTrace_2968663 : CollatzResearch.WordTrace tailWord_2968663 prefixEnd_2968663 1524351020218423826059873 := by
  unfold tailWord_2968663
  simp only [CollatzResearch.WordTrace]
  refine ⟨108276034844048433120598643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72184023229365622080399095 108276034844048433120598643)
  ·
    refine ⟨162414052266072649680897965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108276034844048433120598643 162414052266072649680897965)
    ·
      refine ⟨60905269599777243630336737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162414052266072649680897965 60905269599777243630336737)
      ·
        refine ⟨45678952199832932722752553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60905269599777243630336737 45678952199832932722752553)
        ·
          refine ⟨34259214149874699542064415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45678952199832932722752553 34259214149874699542064415)
          ·
            refine ⟨51388821224812049313096623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34259214149874699542064415 51388821224812049313096623)
            ·
              refine ⟨77083231837218073969644935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51388821224812049313096623 77083231837218073969644935)
              ·
                refine ⟨115624847755827110954467403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77083231837218073969644935 115624847755827110954467403)
                ·
                  refine ⟨173437271633740666431701105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115624847755827110954467403 173437271633740666431701105)
                  ·
                    refine ⟨130077953725305499823775829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173437271633740666431701105 130077953725305499823775829)
                    ·
                      refine ⟨1524351020218423826059873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 130077953725305499823775829 1524351020218423826059873)
                      ·
                        rfl

theorem cell23_2968663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2968663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968663 prefixEnd_2968663 := by exact prefixLift 2968663
  have htrace : WordTrace (prefixWord ++ tailWord_2968663) baseStart_2968663 baseEnd_2968663 := by
    simpa [prefixWord, tailWord_2968663, baseEnd_2968663] using wordTrace_append hprefix tailTrace_2968663
  have hstable : (prefixWord ++ tailWord_2968663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968663).length < 2 ^ (prefixWord ++ tailWord_2968663).sum := by decide
  have hdescent : baseEnd_2968663 < baseStart_2968663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968674 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2968674 : Nat := 118140960795 + 2968674 * 2 ^ 59
def prefixEnd_2968674 : Nat := 4983230072969 + 3 ^ 40 * 2968674 * 2
def baseEnd_2968674 : Nat := 1524356668505623283022323

theorem tailTrace_2968674 : CollatzResearch.WordTrace tailWord_2968674 prefixEnd_2968674 1524356668505623283022323 := by
  unfold tailWord_2968674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27069109011752145499812269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72184290698005721332832717 27069109011752145499812269)
  ·
    refine ⟨10150915879407054562429601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27069109011752145499812269 10150915879407054562429601)
    ·
      refine ⟨7613186909555290921822201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10150915879407054562429601 7613186909555290921822201)
      ·
        refine ⟨5709890182166468191366651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7613186909555290921822201 5709890182166468191366651)
        ·
          refine ⟨8564835273249702287049977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709890182166468191366651 8564835273249702287049977)
          ·
            refine ⟨6423626454937276715287483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8564835273249702287049977 6423626454937276715287483)
            ·
              refine ⟨9635439682405915072931225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423626454937276715287483 9635439682405915072931225)
              ·
                refine ⟨7226579761804436304698419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9635439682405915072931225 7226579761804436304698419)
                ·
                  refine ⟨10839869642706654457047629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226579761804436304698419 10839869642706654457047629)
                  ·
                    refine ⟨4064951116014995421392861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10839869642706654457047629 4064951116014995421392861)
                    ·
                      refine ⟨1524356668505623283022323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064951116014995421392861 1524356668505623283022323)
                      ·
                        rfl

theorem cell23_2968674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2968674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968674 prefixEnd_2968674 := by exact prefixLift 2968674
  have htrace : WordTrace (prefixWord ++ tailWord_2968674) baseStart_2968674 baseEnd_2968674 := by
    simpa [prefixWord, tailWord_2968674, baseEnd_2968674] using wordTrace_append hprefix tailTrace_2968674
  have hstable : (prefixWord ++ tailWord_2968674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968674).length < 2 ^ (prefixWord ++ tailWord_2968674).sum := by decide
  have hdescent : baseEnd_2968674 < baseStart_2968674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968690 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_2968690 : Nat := 118140960795 + 2968690 * 2 ^ 59
def prefixEnd_2968690 : Nat := 4983230072969 + 3 ^ 40 * 2968690 * 2
def baseEnd_2968690 : Nat := 508121628065365073474083

theorem tailTrace_2968690 : CollatzResearch.WordTrace tailWord_2968690 prefixEnd_2968690 508121628065365073474083 := by
  unfold tailWord_2968690
  simp only [CollatzResearch.WordTrace]
  refine ⟨27069254903737654182957881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72184679743300411154554349 27069254903737654182957881)
  ·
    refine ⟨20301941177803240637218411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27069254903737654182957881 20301941177803240637218411)
    ·
      refine ⟨30452911766704860955827617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20301941177803240637218411 30452911766704860955827617)
      ·
        refine ⟨22839683825028645716870713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30452911766704860955827617 22839683825028645716870713)
        ·
          refine ⟨17129762868771484287653035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22839683825028645716870713 17129762868771484287653035)
          ·
            refine ⟨25694644303157226431479553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17129762868771484287653035 25694644303157226431479553)
            ·
              refine ⟨19270983227367919823609665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25694644303157226431479553 19270983227367919823609665)
              ·
                refine ⟨14453237420525939867707249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19270983227367919823609665 14453237420525939867707249)
                ·
                  refine ⟨10839928065394454900780437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14453237420525939867707249 10839928065394454900780437)
                  ·
                    refine ⟨508121628065365073474083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10839928065394454900780437 508121628065365073474083)
                    ·
                      rfl

theorem cell23_2968690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_2968690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968690 prefixEnd_2968690 := by exact prefixLift 2968690
  have htrace : WordTrace (prefixWord ++ tailWord_2968690) baseStart_2968690 baseEnd_2968690 := by
    simpa [prefixWord, tailWord_2968690, baseEnd_2968690] using wordTrace_append hprefix tailTrace_2968690
  have hstable : (prefixWord ++ tailWord_2968690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968690).length < 2 ^ (prefixWord ++ tailWord_2968690).sum := by decide
  have hdescent : baseEnd_2968690 < baseStart_2968690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968700 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_2968700 : Nat := 118140960795 + 2968700 * 2 ^ 59
def prefixEnd_2968700 : Nat := 4983230072969 + 3 ^ 40 * 2968700 * 2
def baseEnd_2968700 : Nat := 1524370019002640181297203

theorem tailTrace_2968700 : CollatzResearch.WordTrace tailWord_2968700 prefixEnd_2968700 1524370019002640181297203 := by
  unfold tailWord_2968700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54138692172457194219847777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72184922896609592293130369 54138692172457194219847777)
  ·
    refine ⟨40604019129342895664885833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54138692172457194219847777 40604019129342895664885833)
    ·
      refine ⟨30453014347007171748664375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40604019129342895664885833 30453014347007171748664375)
      ·
        refine ⟨45679521520510757622996563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30453014347007171748664375 45679521520510757622996563)
        ·
          refine ⟨68519282280766136434494845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45679521520510757622996563 68519282280766136434494845)
          ·
            refine ⟨25694730855287301162935567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68519282280766136434494845 25694730855287301162935567)
            ·
              refine ⟨38542096282930951744403351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25694730855287301162935567 38542096282930951744403351)
              ·
                refine ⟨57813144424396427616605027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38542096282930951744403351 57813144424396427616605027)
                ·
                  refine ⟨86719716636594641424907541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57813144424396427616605027 86719716636594641424907541)
                  ·
                    refine ⟨4064986717340373816792541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86719716636594641424907541 4064986717340373816792541)
                    ·
                      refine ⟨1524370019002640181297203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4064986717340373816792541 1524370019002640181297203)
                      ·
                        rfl

theorem cell23_2968700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_2968700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968700 prefixEnd_2968700 := by exact prefixLift 2968700
  have htrace : WordTrace (prefixWord ++ tailWord_2968700) baseStart_2968700 baseEnd_2968700 := by
    simpa [prefixWord, tailWord_2968700, baseEnd_2968700] using wordTrace_append hprefix tailTrace_2968700
  have hstable : (prefixWord ++ tailWord_2968700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968700).length < 2 ^ (prefixWord ++ tailWord_2968700).sum := by decide
  have hdescent : baseEnd_2968700 < baseStart_2968700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968703 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 13]
def baseStart_2968703 : Nat := 118140960795 + 2968703 * 2 ^ 59
def prefixEnd_2968703 : Nat := 4983230072969 + 3 ^ 40 * 2968703 * 2
def baseEnd_2968703 : Nat := 169374617716067074395521

theorem tailTrace_2968703 : CollatzResearch.WordTrace tailWord_2968703 prefixEnd_2968703 169374617716067074395521 := by
  unfold tailWord_2968703
  simp only [CollatzResearch.WordTrace]
  refine ⟨108277493763903519952054763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72184995842602346634703175 108277493763903519952054763)
  ·
    refine ⟨162416240645855279928082145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108277493763903519952054763 162416240645855279928082145)
    ·
      refine ⟨121812180484391459946061609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162416240645855279928082145 121812180484391459946061609)
      ·
        refine ⟨91359135363293594959546207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121812180484391459946061609 91359135363293594959546207)
        ·
          refine ⟨137038703044940392439319311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91359135363293594959546207 137038703044940392439319311)
          ·
            refine ⟨205558054567410588658978967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137038703044940392439319311 205558054567410588658978967)
            ·
              refine ⟨308337081851115882988468451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205558054567410588658978967 308337081851115882988468451)
              ·
                refine ⟨462505622776673824482702677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308337081851115882988468451 462505622776673824482702677)
                ·
                  refine ⟨169374617716067074395521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 462505622776673824482702677 169374617716067074395521)
                  ·
                    rfl

theorem cell23_2968703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 13].length) (baseStart_2968703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968703 prefixEnd_2968703 := by exact prefixLift 2968703
  have htrace : WordTrace (prefixWord ++ tailWord_2968703) baseStart_2968703 baseEnd_2968703 := by
    simpa [prefixWord, tailWord_2968703, baseEnd_2968703] using wordTrace_append hprefix tailTrace_2968703
  have hstable : (prefixWord ++ tailWord_2968703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968703).length < 2 ^ (prefixWord ++ tailWord_2968703).sum := by decide
  have hdescent : baseEnd_2968703 < baseStart_2968703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968714 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_2968714 : Nat := 118140960795 + 2968714 * 2 ^ 59
def prefixEnd_2968714 : Nat := 4983230072969 + 3 ^ 40 * 2968714 * 2
def baseEnd_2968714 : Nat := 1524377207731803126522139

theorem tailTrace_2968714 : CollatzResearch.WordTrace tailWord_2968714 prefixEnd_2968714 1524377207731803126522139 := by
  unfold tailWord_2968714
  simp only [CollatzResearch.WordTrace]
  refine ⟨27069473741715917207676299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72185263311242445887136797 27069473741715917207676299)
  ·
    refine ⟨40604210612573875811514449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27069473741715917207676299 40604210612573875811514449)
    ·
      refine ⟨30453157959430406858635837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40604210612573875811514449 30453157959430406858635837)
      ·
        refine ⟨11419934234786402571988439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30453157959430406858635837 11419934234786402571988439)
        ·
          refine ⟨17129901352179603857982659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11419934234786402571988439 17129901352179603857982659)
          ·
            refine ⟨25694852028269405786973989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17129901352179603857982659 25694852028269405786973989)
            ·
              refine ⟨4817784755300513585057623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25694852028269405786973989 4817784755300513585057623)
              ·
                refine ⟨7226677132950770377586435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817784755300513585057623 7226677132950770377586435)
                ·
                  refine ⟨10840015699426155566379653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226677132950770377586435 10840015699426155566379653)
                  ·
                    refine ⟨2032502943642404168696185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10840015699426155566379653 2032502943642404168696185)
                    ·
                      refine ⟨1524377207731803126522139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032502943642404168696185 1524377207731803126522139)
                      ·
                        rfl

theorem cell23_2968714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_2968714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968714 prefixEnd_2968714 := by exact prefixLift 2968714
  have htrace : WordTrace (prefixWord ++ tailWord_2968714) baseStart_2968714 baseEnd_2968714 := by
    simpa [prefixWord, tailWord_2968714, baseEnd_2968714] using wordTrace_append hprefix tailTrace_2968714
  have hstable : (prefixWord ++ tailWord_2968714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968714).length < 2 ^ (prefixWord ++ tailWord_2968714).sum := by decide
  have hdescent : baseEnd_2968714 < baseStart_2968714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968735 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2968735 : Nat := 118140960795 + 2968735 * 2 ^ 59
def prefixEnd_2968735 : Nat := 4983230072969 + 3 ^ 40 * 2968735 * 2
def baseEnd_2968735 : Nat := 1524387990825547544359543

theorem tailTrace_2968735 : CollatzResearch.WordTrace tailWord_2968735 prefixEnd_2968735 1524387990825547544359543 := by
  unfold tailWord_2968735
  simp only [CollatzResearch.WordTrace]
  refine ⟨108278660899787589417219659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72185773933191726278146439 108278660899787589417219659)
  ·
    refine ⟨162417991349681384125829489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108278660899787589417219659 162417991349681384125829489)
    ·
      refine ⟨121813493512261038094372117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162417991349681384125829489 121813493512261038094372117)
      ·
        refine ⟨5710007508387236160673693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121813493512261038094372117 5710007508387236160673693)
        ·
          refine ⟨2141252815645213560252635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5710007508387236160673693 2141252815645213560252635)
          ·
            refine ⟨3211879223467820340378953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141252815645213560252635 3211879223467820340378953)
            ·
              refine ⟨2408909417600865255284215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211879223467820340378953 2408909417600865255284215)
              ·
                refine ⟨3613364126401297882926323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408909417600865255284215 3613364126401297882926323)
                ·
                  refine ⟨5420046189601946824389485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613364126401297882926323 5420046189601946824389485)
                  ·
                    refine ⟨2032517321100730059146057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5420046189601946824389485 2032517321100730059146057)
                    ·
                      refine ⟨1524387990825547544359543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032517321100730059146057 1524387990825547544359543)
                      ·
                        rfl

theorem cell23_2968735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2968735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968735 prefixEnd_2968735 := by exact prefixLift 2968735
  have htrace : WordTrace (prefixWord ++ tailWord_2968735) baseStart_2968735 baseEnd_2968735 := by
    simpa [prefixWord, tailWord_2968735, baseEnd_2968735] using wordTrace_append hprefix tailTrace_2968735
  have hstable : (prefixWord ++ tailWord_2968735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968735).length < 2 ^ (prefixWord ++ tailWord_2968735).sum := by decide
  have hdescent : baseEnd_2968735 < baseStart_2968735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
