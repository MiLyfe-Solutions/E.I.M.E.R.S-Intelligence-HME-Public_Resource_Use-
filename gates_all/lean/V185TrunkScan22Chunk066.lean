import V185TrunkScan22Chunk065

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_594002 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_594002 : Nat := 118140960795 + 594002 * 2 ^ 59
def prefixEnd_594002 : Nat := 4983230072969 + 3 ^ 40 * 594002 * 2
def baseEnd_594002 : Nat := 203339023821393465428827

theorem tailTrace_594002 : CollatzResearch.WordTrace tailWord_594002 prefixEnd_594002 203339023821393465428827 := by
  unfold tailWord_594002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416258198509919077516065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14443355196026450873376173 5416258198509919077516065)
  ·
    refine ⟨4062193648882439308137049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5416258198509919077516065 4062193648882439308137049)
    ·
      refine ⟨3046645236661829481102787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4062193648882439308137049 3046645236661829481102787)
      ·
        refine ⟨4569967854992744221654181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3046645236661829481102787 4569967854992744221654181)
        ·
          refine ⟨856868972811139541560159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4569967854992744221654181 856868972811139541560159)
          ·
            refine ⟨1285303459216709312340239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856868972811139541560159 1285303459216709312340239)
            ·
              refine ⟨1927955188825063968510359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285303459216709312340239 1927955188825063968510359)
              ·
                refine ⟨2891932783237595952765539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927955188825063968510359 2891932783237595952765539)
                ·
                  refine ⟨4337899174856393929148309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891932783237595952765539 4337899174856393929148309)
                  ·
                    refine ⟨203339023821393465428827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4337899174856393929148309 203339023821393465428827)
                    ·
                      rfl

theorem cell22_594002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_594002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594002 prefixEnd_594002 := by exact prefixLift 594002
  have htrace : WordTrace (prefixWord ++ tailWord_594002) baseStart_594002 baseEnd_594002 := by
    simpa [prefixWord, tailWord_594002, baseEnd_594002] using wordTrace_append hprefix tailTrace_594002
  have hstable : (prefixWord ++ tailWord_594002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594002).length < 2 ^ (prefixWord ++ tailWord_594002).sum := by decide
  have hdescent : baseEnd_594002 < baseStart_594002 := by decide
  rcases family_descends (prefixWord ++ tailWord_594002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594006 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_594006 : Nat := 118140960795 + 594006 * 2 ^ 59
def prefixEnd_594006 : Nat := 4983230072969 + 3 ^ 40 * 594006 * 2
def baseEnd_594006 : Nat := 67780131034379596109605

theorem tailTrace_594006 : CollatzResearch.WordTrace tailWord_594006 prefixEnd_594006 67780131034379596109605 := by
  unfold tailWord_594006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354073667876574062075617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14443452457350123328806581 1354073667876574062075617)
  ·
    refine ⟨1015555250907430546556713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1354073667876574062075617 1015555250907430546556713)
    ·
      refine ⟨761666438180572909917535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1015555250907430546556713 761666438180572909917535)
      ·
        refine ⟨1142499657270859364876303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761666438180572909917535 1142499657270859364876303)
        ·
          refine ⟨1713749485906289047314455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142499657270859364876303 1713749485906289047314455)
          ·
            refine ⟨2570624228859433570971683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713749485906289047314455 2570624228859433570971683)
            ·
              refine ⟨3855936343289150356457525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570624228859433570971683 3855936343289150356457525)
              ·
                refine ⟨361494032183357845917893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3855936343289150356457525 361494032183357845917893)
                ·
                  refine ⟨67780131034379596109605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361494032183357845917893 67780131034379596109605)
                  ·
                    rfl

theorem cell22_594006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_594006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594006 prefixEnd_594006 := by exact prefixLift 594006
  have htrace : WordTrace (prefixWord ++ tailWord_594006) baseStart_594006 baseEnd_594006 := by
    simpa [prefixWord, tailWord_594006, baseEnd_594006] using wordTrace_append hprefix tailTrace_594006
  have hstable : (prefixWord ++ tailWord_594006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594006).length < 2 ^ (prefixWord ++ tailWord_594006).sum := by decide
  have hdescent : baseEnd_594006 < baseStart_594006 := by decide
  rcases family_descends (prefixWord ++ tailWord_594006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594032 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_594032 : Nat := 118140960795 + 594032 * 2 ^ 59
def prefixEnd_594032 : Nat := 4983230072969 + 3 ^ 40 * 594032 * 2
def baseEnd_594032 : Nat := 203349293434483387178735

theorem tailTrace_594032 : CollatzResearch.WordTrace tailWord_594032 prefixEnd_594032 203349293434483387178735 := by
  unfold tailWord_594032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10833063491965495716828175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14444084655953994289104233 10833063491965495716828175)
  ·
    refine ⟨16249595237948243575242263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10833063491965495716828175 16249595237948243575242263)
    ·
      refine ⟨24374392856922365362863395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16249595237948243575242263 24374392856922365362863395)
      ·
        refine ⟨36561589285383548044295093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24374392856922365362863395 36561589285383548044295093)
        ·
          refine ⟨3427648995504707629152665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36561589285383548044295093 3427648995504707629152665)
          ·
            refine ⟨2570736746628530721864499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3427648995504707629152665 2570736746628530721864499)
            ·
              refine ⟨3856105119942796082796749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570736746628530721864499 3856105119942796082796749)
              ·
                refine ⟨1446039419978548531048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3856105119942796082796749 1446039419978548531048781)
                ·
                  refine ⟨542264782491955699143293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1446039419978548531048781 542264782491955699143293)
                  ·
                    refine ⟨203349293434483387178735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542264782491955699143293 203349293434483387178735)
                    ·
                      rfl

theorem cell22_594032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_594032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594032 prefixEnd_594032 := by exact prefixLift 594032
  have htrace : WordTrace (prefixWord ++ tailWord_594032) baseStart_594032 baseEnd_594032 := by
    simpa [prefixWord, tailWord_594032, baseEnd_594032] using wordTrace_append hprefix tailTrace_594032
  have hstable : (prefixWord ++ tailWord_594032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594032).length < 2 ^ (prefixWord ++ tailWord_594032).sum := by decide
  have hdescent : baseEnd_594032 < baseStart_594032 := by decide
  rcases family_descends (prefixWord ++ tailWord_594032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594070 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_594070 : Nat := 118140960795 + 594070 * 2 ^ 59
def prefixEnd_594070 : Nat := 4983230072969 + 3 ^ 40 * 594070 * 2
def baseEnd_594070 : Nat := 203362301611063954728619

theorem tailTrace_594070 : CollatzResearch.WordTrace tailWord_594070 prefixEnd_594070 203362301611063954728619 := by
  unfold tailWord_594070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354219559862082745221229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14445008638528882615693109 1354219559862082745221229)
  ·
    refine ⟨507832334948281029457961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1354219559862082745221229 507832334948281029457961)
    ·
      refine ⟨380874251211210772093471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 507832334948281029457961 380874251211210772093471)
      ·
        refine ⟨571311376816816158140207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380874251211210772093471 571311376816816158140207)
        ·
          refine ⟨856967065225224237210311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571311376816816158140207 856967065225224237210311)
          ·
            refine ⟨1285450597837836355815467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856967065225224237210311 1285450597837836355815467)
            ·
              refine ⟨1928175896756754533723201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285450597837836355815467 1928175896756754533723201)
              ·
                refine ⟨1446131922567565900292401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928175896756754533723201 1446131922567565900292401)
                ·
                  refine ⟨1084598941925674425219301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1446131922567565900292401 1084598941925674425219301)
                  ·
                    refine ⟨203362301611063954728619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1084598941925674425219301 203362301611063954728619)
                    ·
                      rfl

theorem cell22_594070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_594070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594070 prefixEnd_594070 := by exact prefixLift 594070
  have htrace : WordTrace (prefixWord ++ tailWord_594070) baseStart_594070 baseEnd_594070 := by
    simpa [prefixWord, tailWord_594070, baseEnd_594070] using wordTrace_append hprefix tailTrace_594070
  have hstable : (prefixWord ++ tailWord_594070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594070).length < 2 ^ (prefixWord ++ tailWord_594070).sum := by decide
  have hdescent : baseEnd_594070 < baseStart_594070 := by decide
  rcases family_descends (prefixWord ++ tailWord_594070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594122 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_594122 : Nat := 118140960795 + 594122 * 2 ^ 59
def prefixEnd_594122 : Nat := 4983230072969 + 3 ^ 40 * 594122 * 2
def baseEnd_594122 : Nat := 203380102273753152428459

theorem tailTrace_594122 : CollatzResearch.WordTrace tailWord_594122 prefixEnd_594122 203380102273753152428459 := by
  unfold tailWord_594122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417352388401234201108155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14446273035736624536288413 5417352388401234201108155)
  ·
    refine ⟨8126028582601851301662233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5417352388401234201108155 8126028582601851301662233)
    ·
      refine ⟨6094521436951388476246675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8126028582601851301662233 6094521436951388476246675)
      ·
        refine ⟨9141782155427082714370013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6094521436951388476246675 9141782155427082714370013)
        ·
          refine ⟨3428168308285156017888755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9141782155427082714370013 3428168308285156017888755)
          ·
            refine ⟨5142252462427734026833133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428168308285156017888755 5142252462427734026833133)
            ·
              refine ⟨1928344673410400260062425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5142252462427734026833133 1928344673410400260062425)
              ·
                refine ⟨1446258505057800195046819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928344673410400260062425 1446258505057800195046819)
                ·
                  refine ⟨2169387757586700292570229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446258505057800195046819 2169387757586700292570229)
                  ·
                    refine ⟨203380102273753152428459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2169387757586700292570229 203380102273753152428459)
                    ·
                      rfl

theorem cell22_594122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_594122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594122 prefixEnd_594122 := by exact prefixLift 594122
  have htrace : WordTrace (prefixWord ++ tailWord_594122) baseStart_594122 baseEnd_594122 := by
    simpa [prefixWord, tailWord_594122, baseEnd_594122] using wordTrace_append hprefix tailTrace_594122
  have hstable : (prefixWord ++ tailWord_594122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594122).length < 2 ^ (prefixWord ++ tailWord_594122).sum := by decide
  have hdescent : baseEnd_594122 < baseStart_594122 := by decide
  rcases family_descends (prefixWord ++ tailWord_594122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594126 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_594126 : Nat := 118140960795 + 594126 * 2 ^ 59
def prefixEnd_594126 : Nat := 4983230072969 + 3 ^ 40 * 594126 * 2
def baseEnd_594126 : Nat := 203381471555498475328447

theorem tailTrace_594126 : CollatzResearch.WordTrace tailWord_594126 prefixEnd_594126 203381471555498475328447 := by
  unfold tailWord_594126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708694430698805685947279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14446370297060296991718821 2708694430698805685947279)
  ·
    refine ⟨4063041646048208528920919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2708694430698805685947279 4063041646048208528920919)
    ·
      refine ⟨6094562469072312793381379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4063041646048208528920919 6094562469072312793381379)
      ·
        refine ⟨9141843703608469190072069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6094562469072312793381379 9141843703608469190072069)
        ·
          refine ⟨1714095694426587973138513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9141843703608469190072069 1714095694426587973138513)
          ·
            refine ⟨1285571770819940979853885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1714095694426587973138513 1285571770819940979853885)
            ·
              refine ⟨482089414057477867445207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285571770819940979853885 482089414057477867445207)
              ·
                refine ⟨723134121086216801167811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482089414057477867445207 723134121086216801167811)
                ·
                  refine ⟨1084701181629325201751717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723134121086216801167811 1084701181629325201751717)
                  ·
                    refine ⟨203381471555498475328447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1084701181629325201751717 203381471555498475328447)
                    ·
                      rfl

theorem cell22_594126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_594126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594126 prefixEnd_594126 := by exact prefixLift 594126
  have htrace : WordTrace (prefixWord ++ tailWord_594126) baseStart_594126 baseEnd_594126 := by
    simpa [prefixWord, tailWord_594126, baseEnd_594126] using wordTrace_append hprefix tailTrace_594126
  have hstable : (prefixWord ++ tailWord_594126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594126).length < 2 ^ (prefixWord ++ tailWord_594126).sum := by decide
  have hdescent : baseEnd_594126 < baseStart_594126 := by decide
  rcases family_descends (prefixWord ++ tailWord_594126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594137 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_594137 : Nat := 118140960795 + 594137 * 2 ^ 59
def prefixEnd_594137 : Nat := 4983230072969 + 3 ^ 40 * 594137 * 2
def baseEnd_594137 : Nat := 203385237080298113303413

theorem tailTrace_594137 : CollatzResearch.WordTrace tailWord_594137 prefixEnd_594137 203385237080298113303413 := by
  unfold tailWord_594137
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669956648550594366228665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14446637765700396244152443 21669956648550594366228665)
  ·
    refine ⟨16252467486412945774671499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21669956648550594366228665 16252467486412945774671499)
    ·
      refine ⟨24378701229619418662007249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16252467486412945774671499 24378701229619418662007249)
      ·
        refine ⟨18284025922214563996505437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24378701229619418662007249 18284025922214563996505437)
        ·
          refine ⟨6856509720830461498689539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18284025922214563996505437 6856509720830461498689539)
          ·
            refine ⟨10284764581245692248034309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856509720830461498689539 10284764581245692248034309)
            ·
              refine ⟨1928393358983567296506433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10284764581245692248034309 1928393358983567296506433)
              ·
                refine ⟨1446295019237675472379825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928393358983567296506433 1446295019237675472379825)
                ·
                  refine ⟨1084721264428256604284869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1446295019237675472379825 1084721264428256604284869)
                  ·
                    refine ⟨203385237080298113303413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1084721264428256604284869 203385237080298113303413)
                    ·
                      rfl

theorem cell22_594137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_594137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594137 prefixEnd_594137 := by exact prefixLift 594137
  have htrace : WordTrace (prefixWord ++ tailWord_594137) baseStart_594137 baseEnd_594137 := by
    simpa [prefixWord, tailWord_594137, baseEnd_594137] using wordTrace_append hprefix tailTrace_594137
  have hstable : (prefixWord ++ tailWord_594137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594137).length < 2 ^ (prefixWord ++ tailWord_594137).sum := by decide
  have hdescent : baseEnd_594137 < baseStart_594137 := by decide
  rcases family_descends (prefixWord ++ tailWord_594137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594141 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 4]
def baseStart_594141 : Nat := 118140960795 + 594141 * 2 ^ 59
def prefixEnd_594141 : Nat := 4983230072969 + 3 ^ 40 * 594141 * 2
def baseEnd_594141 : Nat := 67795535454014478734467

theorem tailTrace_594141 : CollatzResearch.WordTrace tailWord_594141 prefixEnd_594141 67795535454014478734467 := by
  unfold tailWord_594141
  simp only [CollatzResearch.WordTrace]
  refine ⟨21670102540536103049374277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14446735027024068699582851 21670102540536103049374277)
  ·
    refine ⟨4063144226350519321757677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21670102540536103049374277 4063144226350519321757677)
    ·
      refine ⟨1523679084881444745659129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4063144226350519321757677 1523679084881444745659129)
      ·
        refine ⟨1142759313661083559244347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1523679084881444745659129 1142759313661083559244347)
        ·
          refine ⟨1714138970491625338866521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142759313661083559244347 1714138970491625338866521)
          ·
            refine ⟨1285604227868719004149891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1714138970491625338866521 1285604227868719004149891)
            ·
              refine ⟨1928406341803078506224837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285604227868719004149891 1928406341803078506224837)
              ·
                refine ⟨361576189088077219917157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1928406341803078506224837 361576189088077219917157)
                ·
                  refine ⟨67795535454014478734467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361576189088077219917157 67795535454014478734467)
                  ·
                    rfl

theorem cell22_594141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_594141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594141 prefixEnd_594141 := by exact prefixLift 594141
  have htrace : WordTrace (prefixWord ++ tailWord_594141) baseStart_594141 baseEnd_594141 := by
    simpa [prefixWord, tailWord_594141, baseEnd_594141] using wordTrace_append hprefix tailTrace_594141
  have hstable : (prefixWord ++ tailWord_594141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594141).length < 2 ^ (prefixWord ++ tailWord_594141).sum := by decide
  have hdescent : baseEnd_594141 < baseStart_594141 := by decide
  rcases family_descends (prefixWord ++ tailWord_594141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594152 : List Nat := [2, 1, 4, 1, 2, 2, 3, 7]
def baseStart_594152 : Nat := 118140960795 + 594152 * 2 ^ 59
def prefixEnd_594152 : Nat := 4983230072969 + 3 ^ 40 * 594152 * 2
def baseEnd_594152 : Nat := 22598930209649230464263

theorem tailTrace_594152 : CollatzResearch.WordTrace tailWord_594152 prefixEnd_594152 22598930209649230464263 := by
  unfold tailWord_594152
  simp only [CollatzResearch.WordTrace]
  refine ⟨10835251871748125964012355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14447002495664167952016473 10835251871748125964012355)
  ·
    refine ⟨16252877807622188946018533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10835251871748125964012355 16252877807622188946018533)
    ·
      refine ⟨3047414588929160427378475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16252877807622188946018533 3047414588929160427378475)
      ·
        refine ⟨4571121883393740641067713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047414588929160427378475 4571121883393740641067713)
        ·
          refine ⟨3428341412545305480800785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4571121883393740641067713 3428341412545305480800785)
          ·
            refine ⟨2571256059408979110600589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3428341412545305480800785 2571256059408979110600589)
            ·
              refine ⟨964221022278367166475221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2571256059408979110600589 964221022278367166475221)
              ·
                refine ⟨22598930209649230464263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 964221022278367166475221 22598930209649230464263)
                ·
                  rfl

theorem cell22_594152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_594152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594152 prefixEnd_594152 := by exact prefixLift 594152
  have htrace : WordTrace (prefixWord ++ tailWord_594152) baseStart_594152 baseEnd_594152 := by
    simpa [prefixWord, tailWord_594152, baseEnd_594152] using wordTrace_append hprefix tailTrace_594152
  have hstable : (prefixWord ++ tailWord_594152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594152).length < 2 ^ (prefixWord ++ tailWord_594152).sum := by decide
  have hdescent : baseEnd_594152 < baseStart_594152 := by decide
  rcases family_descends (prefixWord ++ tailWord_594152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594336 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_594336 : Nat := 118140960795 + 594336 * 2 ^ 59
def prefixEnd_594336 : Nat := 4983230072969 + 3 ^ 40 * 594336 * 2
def baseEnd_594336 : Nat := 203453358847127927577803

theorem tailTrace_594336 : CollatzResearch.WordTrace tailWord_594336 prefixEnd_594336 203453358847127927577803 := by
  unfold tailWord_594336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10838607387414825676361431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14451476516553100901815241 10838607387414825676361431)
  ·
    refine ⟨16257911081122238514542147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10838607387414825676361431 16257911081122238514542147)
    ·
      refine ⟨24386866621683357771813221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16257911081122238514542147 24386866621683357771813221)
      ·
        refine ⟨4572537491565629582214979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24386866621683357771813221 4572537491565629582214979)
        ·
          refine ⟨6858806237348444373322469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572537491565629582214979 6858806237348444373322469)
          ·
            refine ⟨1286026169502833319997963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6858806237348444373322469 1286026169502833319997963)
            ·
              refine ⟨1929039254254249979996945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286026169502833319997963 1929039254254249979996945)
              ·
                refine ⟨1446779440690687484997709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929039254254249979996945 1446779440690687484997709)
                ·
                  refine ⟨542542290259007806874141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1446779440690687484997709 542542290259007806874141)
                  ·
                    refine ⟨203453358847127927577803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542542290259007806874141 203453358847127927577803)
                    ·
                      rfl

theorem cell22_594336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_594336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594336 prefixEnd_594336 := by exact prefixLift 594336
  have htrace : WordTrace (prefixWord ++ tailWord_594336) baseStart_594336 baseEnd_594336 := by
    simpa [prefixWord, tailWord_594336, baseEnd_594336] using wordTrace_append hprefix tailTrace_594336
  have hstable : (prefixWord ++ tailWord_594336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594336).length < 2 ^ (prefixWord ++ tailWord_594336).sum := by decide
  have hdescent : baseEnd_594336 < baseStart_594336 := by decide
  rcases family_descends (prefixWord ++ tailWord_594336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594353 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 1, 3]
def baseStart_594353 : Nat := 118140960795 + 594353 * 2 ^ 59
def prefixEnd_594353 : Nat := 4983230072969 + 3 ^ 40 * 594353 * 2
def baseEnd_594353 : Nat := 203459178294545549902751

theorem tailTrace_594353 : CollatzResearch.WordTrace tailWord_594353 prefixEnd_594353 203459178294545549902751 := by
  unfold tailWord_594353
  simp only [CollatzResearch.WordTrace]
  refine ⟨21677834815768063256091713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14451889877178708837394475 21677834815768063256091713)
  ·
    refine ⟨16258376111826047442068785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21677834815768063256091713 16258376111826047442068785)
    ·
      refine ⟨12193782083869535581551589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16258376111826047442068785 12193782083869535581551589)
      ·
        refine ⟨2286334140725537921540923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12193782083869535581551589 2286334140725537921540923)
        ·
          refine ⟨3429501211088306882311385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286334140725537921540923 3429501211088306882311385)
          ·
            refine ⟨2572125908316230161733539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3429501211088306882311385 2572125908316230161733539)
            ·
              refine ⟨3858188862474345242600309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572125908316230161733539 3858188862474345242600309)
              ·
                refine ⟨361705205856969866493779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3858188862474345242600309 361705205856969866493779)
                ·
                  refine ⟨542557808785454799740669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361705205856969866493779 542557808785454799740669)
                  ·
                    refine ⟨203459178294545549902751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542557808785454799740669 203459178294545549902751)
                    ·
                      rfl

theorem cell22_594353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_594353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594353 prefixEnd_594353 := by exact prefixLift 594353
  have htrace : WordTrace (prefixWord ++ tailWord_594353) baseStart_594353 baseEnd_594353 := by
    simpa [prefixWord, tailWord_594353, baseEnd_594353] using wordTrace_append hprefix tailTrace_594353
  have hstable : (prefixWord ++ tailWord_594353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594353).length < 2 ^ (prefixWord ++ tailWord_594353).sum := by decide
  have hdescent : baseEnd_594353 < baseStart_594353 := by decide
  rcases family_descends (prefixWord ++ tailWord_594353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594366 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_594366 : Nat := 118140960795 + 594366 * 2 ^ 59
def prefixEnd_594366 : Nat := 4983230072969 + 3 ^ 40 * 594366 * 2
def baseEnd_594366 : Nat := 67821209486739283109237

theorem tailTrace_594366 : CollatzResearch.WordTrace tailWord_594366 prefixEnd_594366 67821209486739283109237 := by
  unfold tailWord_594366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709788620590120809539369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14452205976480644317543301 2709788620590120809539369)
  ·
    refine ⟨2032341465442590607154527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2709788620590120809539369 2032341465442590607154527)
    ·
      refine ⟨3048512198163885910731791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032341465442590607154527 3048512198163885910731791)
      ·
        refine ⟨4572768297245828866097687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048512198163885910731791 4572768297245828866097687)
        ·
          refine ⟨6859152445868743299146531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572768297245828866097687 6859152445868743299146531)
          ·
            refine ⟨10288728668803114948719797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6859152445868743299146531 10288728668803114948719797)
            ·
              refine ⟨964568312700292026442481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10288728668803114948719797 964568312700292026442481)
              ·
                refine ⟨723426234525219019831861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964568312700292026442481 723426234525219019831861)
                ·
                  refine ⟨67821209486739283109237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723426234525219019831861 67821209486739283109237)
                  ·
                    rfl

theorem cell22_594366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_594366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594366 prefixEnd_594366 := by exact prefixLift 594366
  have htrace : WordTrace (prefixWord ++ tailWord_594366) baseStart_594366 baseEnd_594366 := by
    simpa [prefixWord, tailWord_594366, baseEnd_594366] using wordTrace_append hprefix tailTrace_594366
  have hstable : (prefixWord ++ tailWord_594366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594366).length < 2 ^ (prefixWord ++ tailWord_594366).sum := by decide
  have hdescent : baseEnd_594366 < baseStart_594366 := by decide
  rcases family_descends (prefixWord ++ tailWord_594366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594394 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_594394 : Nat := 118140960795 + 594394 * 2 ^ 59
def prefixEnd_594394 : Nat := 4983230072969 + 3 ^ 40 * 594394 * 2
def baseEnd_594394 : Nat := 67824404477478369875875

theorem tailTrace_594394 : CollatzResearch.WordTrace tailWord_594394 prefixEnd_594394 67824404477478369875875 := by
  unfold tailWord_594394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5419832552154881814583559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14452886805746351505556157 5419832552154881814583559)
  ·
    refine ⟨8129748828232322721875339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5419832552154881814583559 8129748828232322721875339)
    ·
      refine ⟨12194623242348484082813009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8129748828232322721875339 12194623242348484082813009)
      ·
        refine ⟨9145967431761363062109757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12194623242348484082813009 9145967431761363062109757)
        ·
          refine ⟨3429737786910511148291159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9145967431761363062109757 3429737786910511148291159)
          ·
            refine ⟨5144606680365766722436739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429737786910511148291159 5144606680365766722436739)
            ·
              refine ⟨7716910020548650083655109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144606680365766722436739 7716910020548650083655109)
              ·
                refine ⟨1446920628852871890685333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7716910020548650083655109 1446920628852871890685333)
                ·
                  refine ⟨67824404477478369875875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1446920628852871890685333 67824404477478369875875)
                  ·
                    rfl

theorem cell22_594394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_594394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594394 prefixEnd_594394 := by exact prefixLift 594394
  have htrace : WordTrace (prefixWord ++ tailWord_594394) baseStart_594394 baseEnd_594394 := by
    simpa [prefixWord, tailWord_594394, baseEnd_594394] using wordTrace_append hprefix tailTrace_594394
  have hstable : (prefixWord ++ tailWord_594394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594394).length < 2 ^ (prefixWord ++ tailWord_594394).sum := by decide
  have hdescent : baseEnd_594394 < baseStart_594394 := by decide
  rcases family_descends (prefixWord ++ tailWord_594394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594413 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_594413 : Nat := 118140960795 + 594413 * 2 ^ 59
def prefixEnd_594413 : Nat := 4983230072969 + 3 ^ 40 * 594413 * 2
def baseEnd_594413 : Nat := 203479717520725393402567

theorem tailTrace_594413 : CollatzResearch.WordTrace tailWord_594413 prefixEnd_594413 203479717520725393402567 := by
  unfold tailWord_594413
  simp only [CollatzResearch.WordTrace]
  refine ⟨21680023195550693503275893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14453348797033795668850595 21680023195550693503275893)
  ·
    refine ⟨2032502174582877515932115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21680023195550693503275893 2032502174582877515932115)
    ·
      refine ⟨3048753261874316273898173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032502174582877515932115 3048753261874316273898173)
      ·
        refine ⟨1143282473202868602711815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3048753261874316273898173 1143282473202868602711815)
        ·
          refine ⟨1714923709804302904067723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143282473202868602711815 1714923709804302904067723)
          ·
            refine ⟨2572385564706454356101585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714923709804302904067723 2572385564706454356101585)
            ·
              refine ⟨1929289173529840767076189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572385564706454356101585 1929289173529840767076189)
              ·
                refine ⟨723483440073690287653571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929289173529840767076189 723483440073690287653571)
                ·
                  refine ⟨1085225160110535431480357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723483440073690287653571 1085225160110535431480357)
                  ·
                    refine ⟨203479717520725393402567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085225160110535431480357 203479717520725393402567)
                    ·
                      rfl

theorem cell22_594413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_594413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594413 prefixEnd_594413 := by exact prefixLift 594413
  have htrace : WordTrace (prefixWord ++ tailWord_594413) baseStart_594413 baseEnd_594413 := by
    simpa [prefixWord, tailWord_594413, baseEnd_594413] using wordTrace_append hprefix tailTrace_594413
  have hstable : (prefixWord ++ tailWord_594413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594413).length < 2 ^ (prefixWord ++ tailWord_594413).sum := by decide
  have hdescent : baseEnd_594413 < baseStart_594413 := by decide
  rcases family_descends (prefixWord ++ tailWord_594413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594443 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 2, 3]
def baseStart_594443 : Nat := 118140960795 + 594443 * 2 ^ 59
def prefixEnd_594443 : Nat := 4983230072969 + 3 ^ 40 * 594443 * 2
def baseEnd_594443 : Nat := 203489987133815315152475

theorem tailTrace_594443 : CollatzResearch.WordTrace tailWord_594443 prefixEnd_594443 203489987133815315152475 := by
  unfold tailWord_594443
  simp only [CollatzResearch.WordTrace]
  refine ⟨21681117385442008626867983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14454078256961339084578655 21681117385442008626867983)
  ·
    refine ⟨32521676078163012940301975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21681117385442008626867983 32521676078163012940301975)
    ·
      refine ⟨48782514117244519410452963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32521676078163012940301975 48782514117244519410452963)
      ·
        refine ⟨73173771175866779115679445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48782514117244519410452963 73173771175866779115679445)
        ·
          refine ⟨1715010261934377635523737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 73173771175866779115679445 1715010261934377635523737)
          ·
            refine ⟨1286257696450783226642803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715010261934377635523737 1286257696450783226642803)
            ·
              refine ⟨1929386544676174839964205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286257696450783226642803 1929386544676174839964205)
              ·
                refine ⟨723519954253565564986577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929386544676174839964205 723519954253565564986577)
                ·
                  refine ⟨542639965690174173739933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723519954253565564986577 542639965690174173739933)
                  ·
                    refine ⟨203489987133815315152475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542639965690174173739933 203489987133815315152475)
                    ·
                      rfl

theorem cell22_594443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 3].length) (baseStart_594443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594443 prefixEnd_594443 := by exact prefixLift 594443
  have htrace : WordTrace (prefixWord ++ tailWord_594443) baseStart_594443 baseEnd_594443 := by
    simpa [prefixWord, tailWord_594443, baseEnd_594443] using wordTrace_append hprefix tailTrace_594443
  have hstable : (prefixWord ++ tailWord_594443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594443).length < 2 ^ (prefixWord ++ tailWord_594443).sum := by decide
  have hdescent : baseEnd_594443 < baseStart_594443 := by decide
  rcases family_descends (prefixWord ++ tailWord_594443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594501 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 5]
def baseStart_594501 : Nat := 118140960795 + 594501 * 2 ^ 59
def prefixEnd_594501 : Nat := 4983230072969 + 3 ^ 40 * 594501 * 2
def baseEnd_594501 : Nat := 67836613906374165734099

theorem tailTrace_594501 : CollatzResearch.WordTrace tailWord_594501 prefixEnd_594501 67836613906374165734099 := by
  unfold tailWord_594501
  simp only [CollatzResearch.WordTrace]
  refine ⟨21683232819231884532479357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14455488546154589688319571 21683232819231884532479357)
  ·
    refine ⟨8131212307211956699679759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21683232819231884532479357 8131212307211956699679759)
    ·
      refine ⟨12196818460817935049519639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8131212307211956699679759 12196818460817935049519639)
      ·
        refine ⟨18295227691226902574279459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12196818460817935049519639 18295227691226902574279459)
        ·
          refine ⟨27442841536840353861419189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18295227691226902574279459 27442841536840353861419189)
          ·
            refine ⟨2572766394078783174508049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27442841536840353861419189 2572766394078783174508049)
            ·
              refine ⟨1929574795559087380881037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572766394078783174508049 1929574795559087380881037)
              ·
                refine ⟨723590548334657767830389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929574795559087380881037 723590548334657767830389)
                ·
                  refine ⟨67836613906374165734099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723590548334657767830389 67836613906374165734099)
                  ·
                    rfl

theorem cell22_594501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_594501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594501 prefixEnd_594501 := by exact prefixLift 594501
  have htrace : WordTrace (prefixWord ++ tailWord_594501) baseStart_594501 baseEnd_594501 := by
    simpa [prefixWord, tailWord_594501, baseEnd_594501] using wordTrace_append hprefix tailTrace_594501
  have hstable : (prefixWord ++ tailWord_594501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594501).length < 2 ^ (prefixWord ++ tailWord_594501).sum := by decide
  have hdescent : baseEnd_594501 < baseStart_594501 := by decide
  rcases family_descends (prefixWord ++ tailWord_594501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594657 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 1, 3]
def baseStart_594657 : Nat := 118140960795 + 594657 * 2 ^ 59
def prefixEnd_594657 : Nat := 4983230072969 + 3 ^ 40 * 594657 * 2
def baseEnd_594657 : Nat := 203563243707190090301819

theorem tailTrace_594657 : CollatzResearch.WordTrace tailWord_594657 prefixEnd_594657 203563243707190090301819 := by
  unfold tailWord_594657
  simp only [CollatzResearch.WordTrace]
  refine ⟨21688922606666723175158225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14459281737777815450105483 21688922606666723175158225)
  ·
    refine ⟨16266691955000042381368669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21688922606666723175158225 16266691955000042381368669)
    ·
      refine ⟨6100009483125015893013251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16266691955000042381368669 6100009483125015893013251)
      ·
        refine ⟨9150014224687523839519877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6100009483125015893013251 9150014224687523839519877)
        ·
          refine ⟨1715627667128910719909977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9150014224687523839519877 1715627667128910719909977)
          ·
            refine ⟨1286720750346683039932483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715627667128910719909977 1286720750346683039932483)
            ·
              refine ⟨1930081125520024559898725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286720750346683039932483 1930081125520024559898725)
              ·
                refine ⟨361890211035004604981011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1930081125520024559898725 361890211035004604981011)
                ·
                  refine ⟨542835316552506907471517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361890211035004604981011 542835316552506907471517)
                  ·
                    refine ⟨203563243707190090301819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542835316552506907471517 203563243707190090301819)
                    ·
                      rfl

theorem cell22_594657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_594657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594657 prefixEnd_594657 := by exact prefixLift 594657
  have htrace : WordTrace (prefixWord ++ tailWord_594657) baseStart_594657 baseEnd_594657 := by
    simpa [prefixWord, tailWord_594657, baseEnd_594657] using wordTrace_append hprefix tailTrace_594657
  have hstable : (prefixWord ++ tailWord_594657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594657).length < 2 ^ (prefixWord ++ tailWord_594657).sum := by decide
  have hdescent : baseEnd_594657 < baseStart_594657 := by decide
  rcases family_descends (prefixWord ++ tailWord_594657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594728 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_594728 : Nat := 118140960795 + 594728 * 2 ^ 59
def prefixEnd_594728 : Nat := 4983230072969 + 3 ^ 40 * 594728 * 2
def baseEnd_594728 : Nat := 203587548458169571776601

theorem tailTrace_594728 : CollatzResearch.WordTrace tailWord_594728 prefixEnd_594728 203587548458169571776601 := by
  unfold tailWord_594728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845756094704751150496419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14461008126273001533995225 10845756094704751150496419)
  ·
    refine ⟨16268634142057126725744629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10845756094704751150496419 16268634142057126725744629)
    ·
      refine ⟨1525184450817855630538559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16268634142057126725744629 1525184450817855630538559)
      ·
        refine ⟨2287776676226783445807839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525184450817855630538559 2287776676226783445807839)
        ·
          refine ⟨3431665014340175168711759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287776676226783445807839 3431665014340175168711759)
          ·
            refine ⟨5147497521510262753067639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431665014340175168711759 5147497521510262753067639)
            ·
              refine ⟨7721246282265394129601459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147497521510262753067639 7721246282265394129601459)
              ·
                refine ⟨11581869423398091194402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721246282265394129601459 11581869423398091194402189)
                ·
                  refine ⟨4343201033774284197900821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11581869423398091194402189 4343201033774284197900821)
                  ·
                    refine ⟨203587548458169571776601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4343201033774284197900821 203587548458169571776601)
                    ·
                      rfl

theorem cell22_594728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_594728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594728 prefixEnd_594728 := by exact prefixLift 594728
  have htrace : WordTrace (prefixWord ++ tailWord_594728) baseStart_594728 baseEnd_594728 := by
    simpa [prefixWord, tailWord_594728, baseEnd_594728] using wordTrace_append hprefix tailTrace_594728
  have hstable : (prefixWord ++ tailWord_594728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594728).length < 2 ^ (prefixWord ++ tailWord_594728).sum := by decide
  have hdescent : baseEnd_594728 < baseStart_594728 := by decide
  rcases family_descends (prefixWord ++ tailWord_594728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594749 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 4]
def baseStart_594749 : Nat := 118140960795 + 594749 * 2 ^ 59
def prefixEnd_594749 : Nat := 4983230072969 + 3 ^ 40 * 594749 * 2
def baseEnd_594749 : Nat := 67864912395777505667179

theorem tailTrace_594749 : CollatzResearch.WordTrace tailWord_594749 prefixEnd_594749 67864912395777505667179 := by
  unfold tailWord_594749
  simp only [CollatzResearch.WordTrace]
  refine ⟨21692278122333422887507301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14461518748222281925004867 21692278122333422887507301)
  ·
    refine ⟨4067302147937516791407619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21692278122333422887507301 4067302147937516791407619)
    ·
      refine ⟨6100953221906275187111429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4067302147937516791407619 6100953221906275187111429)
      ·
        refine ⟨1143928729107426597583393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6100953221906275187111429 1143928729107426597583393)
        ·
          refine ⟨857946546830569948187545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1143928729107426597583393 857946546830569948187545)
          ·
            refine ⟨643459910122927461140659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857946546830569948187545 643459910122927461140659)
            ·
              refine ⟨965189865184391191710989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643459910122927461140659 965189865184391191710989)
              ·
                refine ⟨361946199444146696891621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 965189865184391191710989 361946199444146696891621)
                ·
                  refine ⟨67864912395777505667179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361946199444146696891621 67864912395777505667179)
                  ·
                    rfl

theorem cell22_594749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_594749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594749 prefixEnd_594749 := by exact prefixLift 594749
  have htrace : WordTrace (prefixWord ++ tailWord_594749) baseStart_594749 baseEnd_594749 := by
    simpa [prefixWord, tailWord_594749, baseEnd_594749] using wordTrace_append hprefix tailTrace_594749
  have hstable : (prefixWord ++ tailWord_594749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594749).length < 2 ^ (prefixWord ++ tailWord_594749).sum := by decide
  have hdescent : baseEnd_594749 < baseStart_594749 := by decide
  rcases family_descends (prefixWord ++ tailWord_594749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594773 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_594773 : Nat := 118140960795 + 594773 * 2 ^ 59
def prefixEnd_594773 : Nat := 4983230072969 + 3 ^ 40 * 594773 * 2
def baseEnd_594773 : Nat := 203602952877804454401463

theorem tailTrace_594773 : CollatzResearch.WordTrace tailWord_594773 prefixEnd_594773 203602952877804454401463 := by
  unfold tailWord_594773
  simp only [CollatzResearch.WordTrace]
  refine ⟨21693153474246474986380973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14462102316164316657587315 21693153474246474986380973)
  ·
    refine ⟨8134932552842428119892865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21693153474246474986380973 8134932552842428119892865)
    ·
      refine ⟨6101199414631821089919649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8134932552842428119892865 6101199414631821089919649)
      ·
        refine ⟨4575899560973865817439737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6101199414631821089919649 4575899560973865817439737)
        ·
          refine ⟨3431924670730399363079803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4575899560973865817439737 3431924670730399363079803)
          ·
            refine ⟨5147887006095599044619705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431924670730399363079803 5147887006095599044619705)
            ·
              refine ⟨3860915254571699283464779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5147887006095599044619705 3860915254571699283464779)
              ·
                refine ⟨5791372881857548925197169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860915254571699283464779 5791372881857548925197169)
                ·
                  refine ⟨4343529661393161693897877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5791372881857548925197169 4343529661393161693897877)
                  ·
                    refine ⟨203602952877804454401463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4343529661393161693897877 203602952877804454401463)
                    ·
                      rfl

theorem cell22_594773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_594773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594773 prefixEnd_594773 := by exact prefixLift 594773
  have htrace : WordTrace (prefixWord ++ tailWord_594773) baseStart_594773 baseEnd_594773 := by
    simpa [prefixWord, tailWord_594773, baseEnd_594773] using wordTrace_append hprefix tailTrace_594773
  have hstable : (prefixWord ++ tailWord_594773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594773).length < 2 ^ (prefixWord ++ tailWord_594773).sum := by decide
  have hdescent : baseEnd_594773 < baseStart_594773 := by decide
  rcases family_descends (prefixWord ++ tailWord_594773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594826 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_594826 : Nat := 118140960795 + 594826 * 2 ^ 59
def prefixEnd_594826 : Nat := 4983230072969 + 3 ^ 40 * 594826 * 2
def baseEnd_594826 : Nat := 203621095860929982826301

theorem tailTrace_594826 : CollatzResearch.WordTrace tailWord_594826 prefixEnd_594826 203621095860929982826301 := by
  unfold tailWord_594826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423771635763616259515083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14463391028702976692040221 5423771635763616259515083)
  ·
    refine ⟨8135657453645424389272625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5423771635763616259515083 8135657453645424389272625)
    ·
      refine ⟨6101743090234068291954469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8135657453645424389272625 6101743090234068291954469)
      ·
        refine ⟨1144076829418887804741463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6101743090234068291954469 1144076829418887804741463)
        ·
          refine ⟨1716115244128331707112195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144076829418887804741463 1716115244128331707112195)
          ·
            refine ⟨2574172866192497560668293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716115244128331707112195 2574172866192497560668293)
            ·
              refine ⟨482657412411093292625305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2574172866192497560668293 482657412411093292625305)
              ·
                refine ⟨361993059308319969468979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482657412411093292625305 361993059308319969468979)
                ·
                  refine ⟨542989588962479954203469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361993059308319969468979 542989588962479954203469)
                  ·
                    refine ⟨203621095860929982826301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542989588962479954203469 203621095860929982826301)
                    ·
                      rfl

theorem cell22_594826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_594826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594826 prefixEnd_594826 := by exact prefixLift 594826
  have htrace : WordTrace (prefixWord ++ tailWord_594826) baseStart_594826 baseEnd_594826 := by
    simpa [prefixWord, tailWord_594826, baseEnd_594826] using wordTrace_append hprefix tailTrace_594826
  have hstable : (prefixWord ++ tailWord_594826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594826).length < 2 ^ (prefixWord ++ tailWord_594826).sum := by decide
  have hdescent : baseEnd_594826 < baseStart_594826 := by decide
  rcases family_descends (prefixWord ++ tailWord_594826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594833 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 6]
def baseStart_594833 : Nat := 118140960795 + 594833 * 2 ^ 59
def prefixEnd_594833 : Nat := 4983230072969 + 3 ^ 40 * 594833 * 2
def baseEnd_594833 : Nat := 67874497367994765967093

theorem tailTrace_594833 : CollatzResearch.WordTrace tailWord_594833 prefixEnd_594833 67874497367994765967093 := by
  unfold tailWord_594833
  simp only [CollatzResearch.WordTrace]
  refine ⟨21695341854029105233565153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14463561236019403489043435 21695341854029105233565153)
  ·
    refine ⟨16271506390521828925173865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21695341854029105233565153 16271506390521828925173865)
    ·
      refine ⟨12203629792891371693880399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16271506390521828925173865 12203629792891371693880399)
      ·
        refine ⟨18305444689337057540820599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12203629792891371693880399 18305444689337057540820599)
        ·
          refine ⟨27458167034005586311230899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18305444689337057540820599 27458167034005586311230899)
          ·
            refine ⟨41187250551008379466846349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27458167034005586311230899 41187250551008379466846349)
            ·
              refine ⟨15445218956628142300067381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41187250551008379466846349 15445218956628142300067381)
              ·
                refine ⟨1447989277183888340631317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15445218956628142300067381 1447989277183888340631317)
                ·
                  refine ⟨67874497367994765967093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1447989277183888340631317 67874497367994765967093)
                  ·
                    rfl

theorem cell22_594833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_594833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594833 prefixEnd_594833 := by exact prefixLift 594833
  have htrace : WordTrace (prefixWord ++ tailWord_594833) baseStart_594833 baseEnd_594833 := by
    simpa [prefixWord, tailWord_594833, baseEnd_594833] using wordTrace_append hprefix tailTrace_594833
  have hstable : (prefixWord ++ tailWord_594833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594833).length < 2 ^ (prefixWord ++ tailWord_594833).sum := by decide
  have hdescent : baseEnd_594833 < baseStart_594833 := by decide
  rcases family_descends (prefixWord ++ tailWord_594833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594850 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_594850 : Nat := 118140960795 + 594850 * 2 ^ 59
def prefixEnd_594850 : Nat := 4983230072969 + 3 ^ 40 * 594850 * 2
def baseEnd_594850 : Nat := 67876437183800640075409

theorem tailTrace_594850 : CollatzResearch.WordTrace tailWord_594850 prefixEnd_594850 67876437183800640075409 := by
  unfold tailWord_594850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423990473741879284233501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14463974596645011424622669 5423990473741879284233501)
  ·
    refine ⟨2033996427653204731587563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5423990473741879284233501 2033996427653204731587563)
    ·
      refine ⟨3050994641479807097381345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033996427653204731587563 3050994641479807097381345)
      ·
        refine ⟨2288245981109855323036009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3050994641479807097381345 2288245981109855323036009)
        ·
          refine ⟨1716184485832391492277007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2288245981109855323036009 1716184485832391492277007)
          ·
            refine ⟨2574276728748587238415511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716184485832391492277007 2574276728748587238415511)
            ·
              refine ⟨3861415093122880857623267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574276728748587238415511 3861415093122880857623267)
              ·
                refine ⟨5792122639684321286434901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861415093122880857623267 5792122639684321286434901)
                ·
                  refine ⟨67876437183800640075409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5792122639684321286434901 67876437183800640075409)
                  ·
                    rfl

theorem cell22_594850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_594850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594850 prefixEnd_594850 := by exact prefixLift 594850
  have htrace : WordTrace (prefixWord ++ tailWord_594850) baseStart_594850 baseEnd_594850 := by
    simpa [prefixWord, tailWord_594850, baseEnd_594850] using wordTrace_append hprefix tailTrace_594850
  have hstable : (prefixWord ++ tailWord_594850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594850).length < 2 ^ (prefixWord ++ tailWord_594850).sum := by decide
  have hdescent : baseEnd_594850 < baseStart_594850 := by decide
  rcases family_descends (prefixWord ++ tailWord_594850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594884 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 6]
def baseStart_594884 : Nat := 118140960795 + 594884 * 2 ^ 59
def prefixEnd_594884 : Nat := 4983230072969 + 3 ^ 40 * 594884 * 2
def baseEnd_594884 : Nat := 67880316815412388292041

theorem tailTrace_594884 : CollatzResearch.WordTrace tailWord_594884 prefixEnd_594884 67880316815412388292041 := by
  unfold tailWord_594884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10848600988422170471835853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14464801317896227295781137 10848600988422170471835853)
  ·
    refine ⟨4068225370658313926938445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10848600988422170471835853 4068225370658313926938445)
    ·
      refine ⟨1525584513996867722601917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4068225370658313926938445 1525584513996867722601917)
      ·
        refine ⟨572094192748825395975719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1525584513996867722601917 572094192748825395975719)
        ·
          refine ⟨858141289123238093963579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572094192748825395975719 858141289123238093963579)
          ·
            refine ⟨1287211933684857140945369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858141289123238093963579 1287211933684857140945369)
            ·
              refine ⟨965408950263642855709027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287211933684857140945369 965408950263642855709027)
              ·
                refine ⟨1448113425395464283563541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965408950263642855709027 1448113425395464283563541)
                ·
                  refine ⟨67880316815412388292041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1448113425395464283563541 67880316815412388292041)
                  ·
                    rfl

theorem cell22_594884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_594884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594884 prefixEnd_594884 := by exact prefixLift 594884
  have htrace : WordTrace (prefixWord ++ tailWord_594884) baseStart_594884 baseEnd_594884 := by
    simpa [prefixWord, tailWord_594884, baseEnd_594884] using wordTrace_append hprefix tailTrace_594884
  have hstable : (prefixWord ++ tailWord_594884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594884).length < 2 ^ (prefixWord ++ tailWord_594884).sum := by decide
  have hdescent : baseEnd_594884 < baseStart_594884 := by decide
  rcases family_descends (prefixWord ++ tailWord_594884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594940 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_594940 : Nat := 118140960795 + 594940 * 2 ^ 59
def prefixEnd_594940 : Nat := 4983230072969 + 3 ^ 40 * 594940 * 2
def baseEnd_594940 : Nat := 67886706796890561825317

theorem tailTrace_594940 : CollatzResearch.WordTrace tailWord_594940 prefixEnd_594940 67886706796890561825317 := by
  unfold tailWord_594940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10849622232320731253855137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14466162976427641671806849 10849622232320731253855137)
  ·
    refine ⟨8137216674240548440391353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10849622232320731253855137 8137216674240548440391353)
    ·
      refine ⟨6102912505680411330293515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8137216674240548440391353 6102912505680411330293515)
      ·
        refine ⟨9154368758520616995440273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6102912505680411330293515 9154368758520616995440273)
        ·
          refine ⟨6865776568890462746580205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9154368758520616995440273 6865776568890462746580205)
          ·
            refine ⟨2574666213333923529967577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6865776568890462746580205 2574666213333923529967577)
            ·
              refine ⟨1930999660000442647475683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574666213333923529967577 1930999660000442647475683)
              ·
                refine ⟨2896499490000663971213525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930999660000442647475683 2896499490000663971213525)
                ·
                  refine ⟨67886706796890561825317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2896499490000663971213525 67886706796890561825317)
                  ·
                    rfl

theorem cell22_594940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_594940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_594940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_594940 prefixEnd_594940 := by exact prefixLift 594940
  have htrace : WordTrace (prefixWord ++ tailWord_594940) baseStart_594940 baseEnd_594940 := by
    simpa [prefixWord, tailWord_594940, baseEnd_594940] using wordTrace_append hprefix tailTrace_594940
  have hstable : (prefixWord ++ tailWord_594940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594940).length < 2 ^ (prefixWord ++ tailWord_594940).sum := by decide
  have hdescent : baseEnd_594940 < baseStart_594940 := by decide
  rcases family_descends (prefixWord ++ tailWord_594940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595038 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_595038 : Nat := 118140960795 + 595038 * 2 ^ 59
def prefixEnd_595038 : Nat := 4983230072969 + 3 ^ 40 * 595038 * 2
def baseEnd_595038 : Nat := 203693667793432096525651

theorem tailTrace_595038 : CollatzResearch.WordTrace tailWord_595038 prefixEnd_595038 203693667793432096525651 := by
  unfold tailWord_595038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712852352285803155597221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14468545878857616829851845 2712852352285803155597221)
  ·
    refine ⟨508659816053588091674479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2712852352285803155597221 508659816053588091674479)
    ·
      refine ⟨762989724080382137511719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508659816053588091674479 762989724080382137511719)
      ·
        refine ⟨1144484586120573206267579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762989724080382137511719 1144484586120573206267579)
        ·
          refine ⟨1716726879180859809401369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144484586120573206267579 1716726879180859809401369)
          ·
            refine ⟨1287545159385644857051027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716726879180859809401369 1287545159385644857051027)
            ·
              refine ⟨1931317739078467285576541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287545159385644857051027 1931317739078467285576541)
              ·
                refine ⟨724244152154425232091203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1931317739078467285576541 724244152154425232091203)
                ·
                  refine ⟨1086366228231637848136805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724244152154425232091203 1086366228231637848136805)
                  ·
                    refine ⟨203693667793432096525651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086366228231637848136805 203693667793432096525651)
                    ·
                      rfl

theorem cell22_595038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_595038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595038 prefixEnd_595038 := by exact prefixLift 595038
  have htrace : WordTrace (prefixWord ++ tailWord_595038) baseStart_595038 baseEnd_595038 := by
    simpa [prefixWord, tailWord_595038, baseEnd_595038] using wordTrace_append hprefix tailTrace_595038
  have hstable : (prefixWord ++ tailWord_595038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595038).length < 2 ^ (prefixWord ++ tailWord_595038).sum := by decide
  have hdescent : baseEnd_595038 < baseStart_595038 := by decide
  rcases family_descends (prefixWord ++ tailWord_595038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595186 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_595186 : Nat := 118140960795 + 595186 * 2 ^ 59
def prefixEnd_595186 : Nat := 4983230072969 + 3 ^ 40 * 595186 * 2
def baseEnd_595186 : Nat := 203744331218009043825197

theorem tailTrace_595186 : CollatzResearch.WordTrace tailWord_595186 prefixEnd_595186 203744331218009043825197 := by
  unfold tailWord_595186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427054205437561630291353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14472144547833497680776941 5427054205437561630291353)
  ·
    refine ⟨4070290654078171222718515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5427054205437561630291353 4070290654078171222718515)
    ·
      refine ⟨6105435981117256834077773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4070290654078171222718515 6105435981117256834077773)
      ·
        refine ⟨2289538492918971312779165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6105435981117256834077773 2289538492918971312779165)
        ·
          refine ⟨858576934844614242292187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2289538492918971312779165 858576934844614242292187)
          ·
            refine ⟨1287865402266921363438281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858576934844614242292187 1287865402266921363438281)
            ·
              refine ⟨965899051700191022578711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287865402266921363438281 965899051700191022578711)
              ·
                refine ⟨1448848577550286533868067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965899051700191022578711 1448848577550286533868067)
                ·
                  refine ⟨2173272866325429800802101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448848577550286533868067 2173272866325429800802101)
                  ·
                    refine ⟨203744331218009043825197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2173272866325429800802101 203744331218009043825197)
                    ·
                      rfl

theorem cell22_595186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_595186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595186 prefixEnd_595186 := by exact prefixLift 595186
  have htrace : WordTrace (prefixWord ++ tailWord_595186) baseStart_595186 baseEnd_595186 := by
    simpa [prefixWord, tailWord_595186, baseEnd_595186] using wordTrace_append hprefix tailTrace_595186
  have hstable : (prefixWord ++ tailWord_595186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595186).length < 2 ^ (prefixWord ++ tailWord_595186).sum := by decide
  have hdescent : baseEnd_595186 < baseStart_595186 := by decide
  rcases family_descends (prefixWord ++ tailWord_595186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595199 : List Nat := [1, 1, 2, 2, 1, 6, 3, 6]
def baseStart_595199 : Nat := 118140960795 + 595199 * 2 ^ 59
def prefixEnd_595199 : Nat := 4983230072969 + 3 ^ 40 * 595199 * 2
def baseEnd_595199 : Nat := 22638753487075704805573

theorem tailTrace_595199 : CollatzResearch.WordTrace tailWord_595199 prefixEnd_595199 22638753487075704805573 := by
  unfold tailWord_595199
  simp only [CollatzResearch.WordTrace]
  refine ⟨21708690970703149741388651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14472460647135433160925767 21708690970703149741388651)
  ·
    refine ⟨32563036456054724612082977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21708690970703149741388651 32563036456054724612082977)
    ·
      refine ⟨24422277342041043459062233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32563036456054724612082977 24422277342041043459062233)
      ·
        refine ⟨18316708006530782594296675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24422277342041043459062233 18316708006530782594296675)
        ·
          refine ⟨27475062009796173891445013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18316708006530782594296675 27475062009796173891445013)
          ·
            refine ⟨1287893531709195651161485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27475062009796173891445013 1287893531709195651161485)
            ·
              refine ⟨482960074390948369185557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1287893531709195651161485 482960074390948369185557)
              ·
                refine ⟨22638753487075704805573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 482960074390948369185557 22638753487075704805573)
                ·
                  rfl

theorem cell22_595199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 6].length) (baseStart_595199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595199 prefixEnd_595199 := by exact prefixLift 595199
  have htrace : WordTrace (prefixWord ++ tailWord_595199) baseStart_595199 baseEnd_595199 := by
    simpa [prefixWord, tailWord_595199, baseEnd_595199] using wordTrace_append hprefix tailTrace_595199
  have hstable : (prefixWord ++ tailWord_595199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595199).length < 2 ^ (prefixWord ++ tailWord_595199).sum := by decide
  have hdescent : baseEnd_595199 < baseStart_595199 := by decide
  rcases family_descends (prefixWord ++ tailWord_595199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595201 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_595201 : Nat := 118140960795 + 595201 * 2 ^ 59
def prefixEnd_595201 : Nat := 4983230072969 + 3 ^ 40 * 595201 * 2
def baseEnd_595201 : Nat := 203749466024554004700151

theorem tailTrace_595201 : CollatzResearch.WordTrace tailWord_595201 prefixEnd_595201 203749466024554004700151 := by
  unfold tailWord_595201
  simp only [CollatzResearch.WordTrace]
  refine ⟨21708763916695904082961457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14472509277797269388640971 21708763916695904082961457)
  ·
    refine ⟨16281572937521928062221093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21708763916695904082961457 16281572937521928062221093)
    ·
      refine ⟨3052794925785361511666455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16281572937521928062221093 3052794925785361511666455)
      ·
        refine ⟨4579192388678042267499683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3052794925785361511666455 4579192388678042267499683)
        ·
          refine ⟨6868788583017063401249525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579192388678042267499683 6868788583017063401249525)
          ·
            refine ⟨643948929657849693867143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6868788583017063401249525 643948929657849693867143)
            ·
              refine ⟨965923394486774540800715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643948929657849693867143 965923394486774540800715)
              ·
                refine ⟨1448885091730161811201073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965923394486774540800715 1448885091730161811201073)
                ·
                  refine ⟨1086663818797621358400805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1448885091730161811201073 1086663818797621358400805)
                  ·
                    refine ⟨203749466024554004700151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086663818797621358400805 203749466024554004700151)
                    ·
                      rfl

theorem cell22_595201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_595201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595201 prefixEnd_595201 := by exact prefixLift 595201
  have htrace : WordTrace (prefixWord ++ tailWord_595201) baseStart_595201 baseEnd_595201 := by
    simpa [prefixWord, tailWord_595201, baseEnd_595201] using wordTrace_append hprefix tailTrace_595201
  have hstable : (prefixWord ++ tailWord_595201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595201).length < 2 ^ (prefixWord ++ tailWord_595201).sum := by decide
  have hdescent : baseEnd_595201 < baseStart_595201 := by decide
  rcases family_descends (prefixWord ++ tailWord_595201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595265 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 1, 3]
def baseStart_595265 : Nat := 118140960795 + 595265 * 2 ^ 59
def prefixEnd_595265 : Nat := 4983230072969 + 3 ^ 40 * 595265 * 2
def baseEnd_595265 : Nat := 203771374532479171099955

theorem tailTrace_595265 : CollatzResearch.WordTrace tailWord_595265 prefixEnd_595265 203771374532479171099955 := by
  unfold tailWord_595265
  simp only [CollatzResearch.WordTrace]
  refine ⟨21711098188464043013291249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14474065458976028675527499 21711098188464043013291249)
  ·
    refine ⟨16283323641348032259968437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21711098188464043013291249 16283323641348032259968437)
    ·
      refine ⟨1526561591376378024372041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16283323641348032259968437 1526561591376378024372041)
      ·
        refine ⟨1144921193532283518279031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1526561591376378024372041 1144921193532283518279031)
        ·
          refine ⟨1717381790298425277418547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144921193532283518279031 1717381790298425277418547)
          ·
            refine ⟨2576072685447637916127821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717381790298425277418547 2576072685447637916127821)
            ·
              refine ⟨966027257042864218547933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2576072685447637916127821 966027257042864218547933)
              ·
                refine ⟨362260221391074081955475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966027257042864218547933 362260221391074081955475)
                ·
                  refine ⟨543390332086611122933213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362260221391074081955475 543390332086611122933213)
                  ·
                    refine ⟨203771374532479171099955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 543390332086611122933213 203771374532479171099955)
                    ·
                      rfl

theorem cell22_595265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_595265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595265 prefixEnd_595265 := by exact prefixLift 595265
  have htrace : WordTrace (prefixWord ++ tailWord_595265) baseStart_595265 baseEnd_595265 := by
    simpa [prefixWord, tailWord_595265, baseEnd_595265] using wordTrace_append hprefix tailTrace_595265
  have hstable : (prefixWord ++ tailWord_595265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595265).length < 2 ^ (prefixWord ++ tailWord_595265).sum := by decide
  have hdescent : baseEnd_595265 < baseStart_595265 := by decide
  rcases family_descends (prefixWord ++ tailWord_595265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595289 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 6]
def baseStart_595289 : Nat := 118140960795 + 595289 * 2 ^ 59
def prefixEnd_595289 : Nat := 4983230072969 + 3 ^ 40 * 595289 * 2
def baseEnd_595289 : Nat := 67926530074317036166627

theorem tailTrace_595289 : CollatzResearch.WordTrace tailWord_595289 prefixEnd_595289 67926530074317036166627 := by
  unfold tailWord_595289
  simp only [CollatzResearch.WordTrace]
  refine ⟨21711973540377095112164921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14474649026918063408109947 21711973540377095112164921)
  ·
    refine ⟨16283980155282821334123691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21711973540377095112164921 16283980155282821334123691)
    ·
      refine ⟨24425970232924232001185537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16283980155282821334123691 24425970232924232001185537)
      ·
        refine ⟨18319477674693174000889153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24425970232924232001185537 18319477674693174000889153)
        ·
          refine ⟨13739608256019880500666865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18319477674693174000889153 13739608256019880500666865)
          ·
            refine ⟨10304706192014910375500149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13739608256019880500666865 10304706192014910375500149)
            ·
              refine ⟨966066205501397847703139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10304706192014910375500149 966066205501397847703139)
              ·
                refine ⟨1449099308252096771554709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966066205501397847703139 1449099308252096771554709)
                ·
                  refine ⟨67926530074317036166627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1449099308252096771554709 67926530074317036166627)
                  ·
                    rfl

theorem cell22_595289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_595289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595289 prefixEnd_595289 := by exact prefixLift 595289
  have htrace : WordTrace (prefixWord ++ tailWord_595289) baseStart_595289 baseEnd_595289 := by
    simpa [prefixWord, tailWord_595289, baseEnd_595289] using wordTrace_append hprefix tailTrace_595289
  have hstable : (prefixWord ++ tailWord_595289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595289).length < 2 ^ (prefixWord ++ tailWord_595289).sum := by decide
  have hdescent : baseEnd_595289 < baseStart_595289 := by decide
  rcases family_descends (prefixWord ++ tailWord_595289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595308 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_595308 : Nat := 118140960795 + 595308 * 2 ^ 59
def prefixEnd_595308 : Nat := 4983230072969 + 3 ^ 40 * 595308 * 2
def baseEnd_595308 : Nat := 203786094311241392274823

theorem tailTrace_595308 : CollatzResearch.WordTrace tailWord_595308 prefixEnd_595308 203786094311241392274823 := by
  unfold tailWord_595308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856333263654130678553289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14475111018205507571404385 10856333263654130678553289)
  ·
    refine ⟨8142249947740598008914967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10856333263654130678553289 8142249947740598008914967)
    ·
      refine ⟨12213374921610897013372451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142249947740598008914967 12213374921610897013372451)
      ·
        refine ⟨18320062382416345520058677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12213374921610897013372451 18320062382416345520058677)
        ·
          refine ⟨1717505848351532392505501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18320062382416345520058677 1717505848351532392505501)
          ·
            refine ⟨644064693131824647189563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1717505848351532392505501 644064693131824647189563)
            ·
              refine ⟨966097039697736970784345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644064693131824647189563 966097039697736970784345)
              ·
                refine ⟨724572779773302728088259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966097039697736970784345 724572779773302728088259)
                ·
                  refine ⟨1086859169659954092132389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724572779773302728088259 1086859169659954092132389)
                  ·
                    refine ⟨203786094311241392274823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086859169659954092132389 203786094311241392274823)
                    ·
                      rfl

theorem cell22_595308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_595308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595308 prefixEnd_595308 := by exact prefixLift 595308
  have htrace : WordTrace (prefixWord ++ tailWord_595308) baseStart_595308 baseEnd_595308 := by
    simpa [prefixWord, tailWord_595308, baseEnd_595308] using wordTrace_append hprefix tailTrace_595308
  have hstable : (prefixWord ++ tailWord_595308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595308).length < 2 ^ (prefixWord ++ tailWord_595308).sum := by decide
  have hdescent : baseEnd_595308 < baseStart_595308 := by decide
  rcases family_descends (prefixWord ++ tailWord_595308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595336 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_595336 : Nat := 118140960795 + 595336 * 2 ^ 59
def prefixEnd_595336 : Nat := 4983230072969 + 3 ^ 40 * 595336 * 2
def baseEnd_595336 : Nat := 203795679283458652574737

theorem tailTrace_595336 : CollatzResearch.WordTrace tailWord_595336 prefixEnd_595336 203795679283458652574737 := by
  unfold tailWord_595336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856843885603411069562931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14475791847471214759417241 10856843885603411069562931)
  ·
    refine ⟨16285265828405116604344397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10856843885603411069562931 16285265828405116604344397)
    ·
      refine ⟨6106974685651918726629149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16285265828405116604344397 6106974685651918726629149)
      ·
        refine ⟨2290115507119469522485931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6106974685651918726629149 2290115507119469522485931)
        ·
          refine ⟨3435173260679204283728897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290115507119469522485931 3435173260679204283728897)
          ·
            refine ⟨2576379945509403212796673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435173260679204283728897 2576379945509403212796673)
            ·
              refine ⟨1932284959132052409597505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576379945509403212796673 1932284959132052409597505)
              ·
                refine ⟨1449213719349039307198129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932284959132052409597505 1449213719349039307198129)
                ·
                  refine ⟨1086910289511779480398597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449213719349039307198129 1086910289511779480398597)
                  ·
                    refine ⟨203795679283458652574737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086910289511779480398597 203795679283458652574737)
                    ·
                      rfl

theorem cell22_595336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_595336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595336 prefixEnd_595336 := by exact prefixLift 595336
  have htrace : WordTrace (prefixWord ++ tailWord_595336) baseStart_595336 baseEnd_595336 := by
    simpa [prefixWord, tailWord_595336, baseEnd_595336] using wordTrace_append hprefix tailTrace_595336
  have hstable : (prefixWord ++ tailWord_595336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595336).length < 2 ^ (prefixWord ++ tailWord_595336).sum := by decide
  have hdescent : baseEnd_595336 < baseStart_595336 := by decide
  rcases family_descends (prefixWord ++ tailWord_595336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595364 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_595364 : Nat := 118140960795 + 595364 * 2 ^ 59
def prefixEnd_595364 : Nat := 4983230072969 + 3 ^ 40 * 595364 * 2
def baseEnd_595364 : Nat := 203805264255675912874651

theorem tailTrace_595364 : CollatzResearch.WordTrace tailWord_595364 prefixEnd_595364 203805264255675912874651 := by
  unfold tailWord_595364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10857354507552691460572573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14476472676736921947430097 10857354507552691460572573)
  ·
    refine ⟨4071507940332259297714715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10857354507552691460572573 4071507940332259297714715)
    ·
      refine ⟨6107261910498388946572073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071507940332259297714715 6107261910498388946572073)
      ·
        refine ⟨4580446432873791709929055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6107261910498388946572073 4580446432873791709929055)
        ·
          refine ⟨6870669649310687564893583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4580446432873791709929055 6870669649310687564893583)
          ·
            refine ⟨10306004473966031347340375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6870669649310687564893583 10306004473966031347340375)
            ·
              refine ⟨15459006710949047021010563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10306004473966031347340375 15459006710949047021010563)
              ·
                refine ⟨23188510066423570531515845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15459006710949047021010563 23188510066423570531515845)
                ·
                  refine ⟨4347845637454419474659221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23188510066423570531515845 4347845637454419474659221)
                  ·
                    refine ⟨203805264255675912874651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4347845637454419474659221 203805264255675912874651)
                    ·
                      rfl

theorem cell22_595364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_595364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595364 prefixEnd_595364 := by exact prefixLift 595364
  have htrace : WordTrace (prefixWord ++ tailWord_595364) baseStart_595364 baseEnd_595364 := by
    simpa [prefixWord, tailWord_595364, baseEnd_595364] using wordTrace_append hprefix tailTrace_595364
  have hstable : (prefixWord ++ tailWord_595364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595364).length < 2 ^ (prefixWord ++ tailWord_595364).sum := by decide
  have hdescent : baseEnd_595364 < baseStart_595364 := by decide
  rcases family_descends (prefixWord ++ tailWord_595364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595413 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 5]
def baseStart_595413 : Nat := 118140960795 + 595413 * 2 ^ 59
def prefixEnd_595413 : Nat := 4983230072969 + 3 ^ 40 * 595413 * 2
def baseEnd_595413 : Nat := 67940679319018706133167

theorem tailTrace_595413 : CollatzResearch.WordTrace tailWord_595413 prefixEnd_595413 67940679319018706133167 := by
  unfold tailWord_595413
  simp only [CollatzResearch.WordTrace]
  refine ⟨21716496191927864289678893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14477664127951909526452595 21716496191927864289678893)
  ·
    refine ⟨8143686071972949108629585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21716496191927864289678893 8143686071972949108629585)
    ·
      refine ⟨6107764553979711831472189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8143686071972949108629585 6107764553979711831472189)
      ·
        refine ⟨2290411707742391936802071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6107764553979711831472189 2290411707742391936802071)
        ·
          refine ⟨3435617561613587905203107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290411707742391936802071 3435617561613587905203107)
          ·
            refine ⟨5153426342420381857804661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435617561613587905203107 5153426342420381857804661)
            ·
              refine ⟨483133719601910799169187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5153426342420381857804661 483133719601910799169187)
              ·
                refine ⟨724700579402866198753781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483133719601910799169187 724700579402866198753781)
                ·
                  refine ⟨67940679319018706133167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 724700579402866198753781 67940679319018706133167)
                  ·
                    rfl

theorem cell22_595413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_595413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595413 prefixEnd_595413 := by exact prefixLift 595413
  have htrace : WordTrace (prefixWord ++ tailWord_595413) baseStart_595413 baseEnd_595413 := by
    simpa [prefixWord, tailWord_595413, baseEnd_595413] using wordTrace_append hprefix tailTrace_595413
  have hstable : (prefixWord ++ tailWord_595413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595413).length < 2 ^ (prefixWord ++ tailWord_595413).sum := by decide
  have hdescent : baseEnd_595413 < baseStart_595413 := by decide
  rcases family_descends (prefixWord ++ tailWord_595413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595424 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_595424 : Nat := 118140960795 + 595424 * 2 ^ 59
def prefixEnd_595424 : Nat := 4983230072969 + 3 ^ 40 * 595424 * 2
def baseEnd_595424 : Nat := 67941934493951918791489

theorem tailTrace_595424 : CollatzResearch.WordTrace tailWord_595424 prefixEnd_595424 67941934493951918791489 := by
  unfold tailWord_595424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10858448697444006584164663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14477931596592008778886217 10858448697444006584164663)
  ·
    refine ⟨16287673046166009876246995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10858448697444006584164663 16287673046166009876246995)
    ·
      refine ⟨24431509569249014814370493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16287673046166009876246995 24431509569249014814370493)
      ·
        refine ⟨9161816088468380555388935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24431509569249014814370493 9161816088468380555388935)
        ·
          refine ⟨13742724132702570833083403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9161816088468380555388935 13742724132702570833083403)
          ·
            refine ⟨20614086199053856249625105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13742724132702570833083403 20614086199053856249625105)
            ·
              refine ⟨15460564649290392187218829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20614086199053856249625105 15460564649290392187218829)
              ·
                refine ⟨5797711743483897070207061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15460564649290392187218829 5797711743483897070207061)
                ·
                  refine ⟨67941934493951918791489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5797711743483897070207061 67941934493951918791489)
                  ·
                    rfl

theorem cell22_595424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_595424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595424 prefixEnd_595424 := by exact prefixLift 595424
  have htrace : WordTrace (prefixWord ++ tailWord_595424) baseStart_595424 baseEnd_595424 := by
    simpa [prefixWord, tailWord_595424, baseEnd_595424] using wordTrace_append hprefix tailTrace_595424
  have hstable : (prefixWord ++ tailWord_595424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595424).length < 2 ^ (prefixWord ++ tailWord_595424).sum := by decide
  have hdescent : baseEnd_595424 < baseStart_595424 := by decide
  rcases family_descends (prefixWord ++ tailWord_595424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595434 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_595434 : Nat := 118140960795 + 595434 * 2 ^ 59
def prefixEnd_595434 : Nat := 4983230072969 + 3 ^ 40 * 595434 * 2
def baseEnd_595434 : Nat := 203829226686219063624437

theorem tailTrace_595434 : CollatzResearch.WordTrace tailWord_595434 prefixEnd_595434 203829226686219063624437 := by
  unfold tailWord_595434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429315531212946219048339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14478174749901189917462237 5429315531212946219048339)
  ·
    refine ⟨8143973296819419328572509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429315531212946219048339 8143973296819419328572509)
    ·
      refine ⟨3053989986307282248214691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8143973296819419328572509 3053989986307282248214691)
      ·
        refine ⟨4580984979460923372322037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053989986307282248214691 4580984979460923372322037)
        ·
          refine ⟨429467341824461566155191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4580984979460923372322037 429467341824461566155191)
          ·
            refine ⟨644201012736692349232787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429467341824461566155191 644201012736692349232787)
            ·
              refine ⟨966301519105038523849181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644201012736692349232787 966301519105038523849181)
              ·
                refine ⟨362363069664389446443443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966301519105038523849181 362363069664389446443443)
                ·
                  refine ⟨543544604496584169665165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362363069664389446443443 543544604496584169665165)
                  ·
                    refine ⟨203829226686219063624437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 543544604496584169665165 203829226686219063624437)
                    ·
                      rfl

theorem cell22_595434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_595434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595434 prefixEnd_595434 := by exact prefixLift 595434
  have htrace : WordTrace (prefixWord ++ tailWord_595434) baseStart_595434 baseEnd_595434 := by
    simpa [prefixWord, tailWord_595434, baseEnd_595434] using wordTrace_append hprefix tailTrace_595434
  have hstable : (prefixWord ++ tailWord_595434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595434).length < 2 ^ (prefixWord ++ tailWord_595434).sum := by decide
  have hdescent : baseEnd_595434 < baseStart_595434 := by decide
  rcases family_descends (prefixWord ++ tailWord_595434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595473 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_595473 : Nat := 118140960795 + 595473 * 2 ^ 59
def prefixEnd_595473 : Nat := 4983230072969 + 3 ^ 40 * 595473 * 2
def baseEnd_595473 : Nat := 203842577183235961899317

theorem tailTrace_595473 : CollatzResearch.WordTrace tailWord_595473 prefixEnd_595473 203842577183235961899317 := by
  unfold tailWord_595473
  simp only [CollatzResearch.WordTrace]
  refine ⟨21718684571710494536863073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14479123047806996357908715 21718684571710494536863073)
  ·
    refine ⟨16289013428782870902647305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21718684571710494536863073 16289013428782870902647305)
    ·
      refine ⟨12216760071587153176985479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16289013428782870902647305 12216760071587153176985479)
      ·
        refine ⟨18325140107380729765478219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216760071587153176985479 18325140107380729765478219)
        ·
          refine ⟨27487710161071094648217329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18325140107380729765478219 27487710161071094648217329)
          ·
            refine ⟨20615782620803320986162997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27487710161071094648217329 20615782620803320986162997)
            ·
              refine ⟨1932729620700311342452781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20615782620803320986162997 1932729620700311342452781)
              ·
                refine ⟨724773607762616753419793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1932729620700311342452781 724773607762616753419793)
                ·
                  refine ⟨543580205821962565064845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724773607762616753419793 543580205821962565064845)
                  ·
                    refine ⟨203842577183235961899317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 543580205821962565064845 203842577183235961899317)
                    ·
                      rfl

theorem cell22_595473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_595473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595473 prefixEnd_595473 := by exact prefixLift 595473
  have htrace : WordTrace (prefixWord ++ tailWord_595473) baseStart_595473 baseEnd_595473 := by
    simpa [prefixWord, tailWord_595473, baseEnd_595473] using wordTrace_append hprefix tailTrace_595473
  have hstable : (prefixWord ++ tailWord_595473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595473).length < 2 ^ (prefixWord ++ tailWord_595473).sum := by decide
  have hdescent : baseEnd_595473 < baseStart_595473 := by decide
  rcases family_descends (prefixWord ++ tailWord_595473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595488 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_595488 : Nat := 118140960795 + 595488 * 2 ^ 59
def prefixEnd_595488 : Nat := 4983230072969 + 3 ^ 40 * 595488 * 2
def baseEnd_595488 : Nat := 203847711989780922774271

theorem tailTrace_595488 : CollatzResearch.WordTrace tailWord_595488 prefixEnd_595488 203847711989780922774271 := by
  unfold tailWord_595488
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859615833328076049329559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14479487777770768065772745 10859615833328076049329559)
  ·
    refine ⟨16289423749992114073994339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10859615833328076049329559 16289423749992114073994339)
    ·
      refine ⟨24434135624988171110991509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16289423749992114073994339 24434135624988171110991509)
      ·
        refine ⟨1145350107421320520827727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24434135624988171110991509 1145350107421320520827727)
        ·
          refine ⟨1718025161131980781241591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145350107421320520827727 1718025161131980781241591)
          ·
            refine ⟨2577037741697971171862387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718025161131980781241591 2577037741697971171862387)
            ·
              refine ⟨3865556612546956757793581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577037741697971171862387 3865556612546956757793581)
              ·
                refine ⟨1449583729705108784172593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865556612546956757793581 1449583729705108784172593)
                ·
                  refine ⟨1087187797278831588129445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449583729705108784172593 1087187797278831588129445)
                  ·
                    refine ⟨203847711989780922774271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087187797278831588129445 203847711989780922774271)
                    ·
                      rfl

theorem cell22_595488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_595488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595488 prefixEnd_595488 := by exact prefixLift 595488
  have htrace : WordTrace (prefixWord ++ tailWord_595488) baseStart_595488 baseEnd_595488 := by
    simpa [prefixWord, tailWord_595488, baseEnd_595488] using wordTrace_append hprefix tailTrace_595488
  have hstable : (prefixWord ++ tailWord_595488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595488).length < 2 ^ (prefixWord ++ tailWord_595488).sum := by decide
  have hdescent : baseEnd_595488 < baseStart_595488 := by decide
  rcases family_descends (prefixWord ++ tailWord_595488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595621 : List Nat := [1, 3, 1, 2, 1, 2, 12]
def baseStart_595621 : Nat := 118140960795 + 595621 * 2 ^ 59
def prefixEnd_595621 : Nat := 4983230072969 + 3 ^ 40 * 595621 * 2
def baseEnd_595621 : Nat := 7551601503993070711069

theorem tailTrace_595621 : CollatzResearch.WordTrace tailWord_595621 prefixEnd_595621 7551601503993070711069 := by
  unfold tailWord_595621
  simp only [CollatzResearch.WordTrace]
  refine ⟨21724082575174315813250717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14482721716782877208833811 21724082575174315813250717)
  ·
    refine ⟨8146530965690368429969019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21724082575174315813250717 8146530965690368429969019)
    ·
      refine ⟨12219796448535552644953529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8146530965690368429969019 12219796448535552644953529)
      ·
        refine ⟨9164847336401664483715147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12219796448535552644953529 9164847336401664483715147)
        ·
          refine ⟨13747271004602496725572721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9164847336401664483715147 13747271004602496725572721)
          ·
            refine ⟨10310453253451872544179541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13747271004602496725572721 10310453253451872544179541)
            ·
              refine ⟨7551601503993070711069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10310453253451872544179541 7551601503993070711069)
              ·
                rfl

theorem cell22_595621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 12].length) (baseStart_595621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595621 prefixEnd_595621 := by exact prefixLift 595621
  have htrace : WordTrace (prefixWord ++ tailWord_595621) baseStart_595621 baseEnd_595621 := by
    simpa [prefixWord, tailWord_595621, baseEnd_595621] using wordTrace_append hprefix tailTrace_595621
  have hstable : (prefixWord ++ tailWord_595621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595621).length < 2 ^ (prefixWord ++ tailWord_595621).sum := by decide
  have hdescent : baseEnd_595621 < baseStart_595621 := by decide
  rcases family_descends (prefixWord ++ tailWord_595621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595642 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_595642 : Nat := 118140960795 + 595642 * 2 ^ 59
def prefixEnd_595642 : Nat := 4983230072969 + 3 ^ 40 * 595642 * 2
def baseEnd_595642 : Nat := 203900429336975854423799

theorem tailTrace_595642 : CollatzResearch.WordTrace tailWord_595642 prefixEnd_595642 203900429336975854423799 := by
  unfold tailWord_595642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5431212127024559099941295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14483232338732157599843453 5431212127024559099941295)
  ·
    refine ⟨8146818190536838649911943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5431212127024559099941295 8146818190536838649911943)
    ·
      refine ⟨12220227285805257974867915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8146818190536838649911943 12220227285805257974867915)
      ·
        refine ⟨18330340928707886962301873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12220227285805257974867915 18330340928707886962301873)
        ·
          refine ⟨13747755696530915221726405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18330340928707886962301873 13747755696530915221726405)
          ·
            refine ⟨2577704193099546604073701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13747755696530915221726405 2577704193099546604073701)
            ·
              refine ⟨483319536206164988263819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2577704193099546604073701 483319536206164988263819)
              ·
                refine ⟨724979304309247482395729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483319536206164988263819 724979304309247482395729)
                ·
                  refine ⟨543734478231935611796797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724979304309247482395729 543734478231935611796797)
                  ·
                    refine ⟨203900429336975854423799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 543734478231935611796797 203900429336975854423799)
                    ·
                      rfl

theorem cell22_595642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_595642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595642 prefixEnd_595642 := by exact prefixLift 595642
  have htrace : WordTrace (prefixWord ++ tailWord_595642) baseStart_595642 baseEnd_595642 := by
    simpa [prefixWord, tailWord_595642, baseEnd_595642] using wordTrace_append hprefix tailTrace_595642
  have hstable : (prefixWord ++ tailWord_595642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595642).length < 2 ^ (prefixWord ++ tailWord_595642).sum := by decide
  have hdescent : baseEnd_595642 < baseStart_595642 := by decide
  rcases family_descends (prefixWord ++ tailWord_595642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595745 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 6]
def baseStart_595745 : Nat := 118140960795 + 595745 * 2 ^ 59
def prefixEnd_595745 : Nat := 4983230072969 + 3 ^ 40 * 595745 * 2
def baseEnd_595745 : Nat := 67978562780639306366161

theorem tailTrace_595745 : CollatzResearch.WordTrace tailWord_595745 prefixEnd_595745 67978562780639306366161 := by
  unfold tailWord_595745
  simp only [CollatzResearch.WordTrace]
  refine ⟨21728605226725084990764689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14485736817816723327176459 21728605226725084990764689)
  ·
    refine ⟨16296453920043813743073517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21728605226725084990764689 16296453920043813743073517)
    ·
      refine ⟨6111170220016430153652569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16296453920043813743073517 6111170220016430153652569)
      ·
        refine ⟨4583377665012322615239427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6111170220016430153652569 4583377665012322615239427)
        ·
          refine ⟨6875066497518483922859141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4583377665012322615239427 6875066497518483922859141)
          ·
            refine ⟨1289074968284715735536089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6875066497518483922859141 1289074968284715735536089)
            ·
              refine ⟨966806226213536801652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289074968284715735536089 966806226213536801652067)
              ·
                refine ⟨1450209339320305202478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966806226213536801652067 1450209339320305202478101)
                ·
                  refine ⟨67978562780639306366161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1450209339320305202478101 67978562780639306366161)
                  ·
                    rfl

theorem cell22_595745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_595745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595745 prefixEnd_595745 := by exact prefixLift 595745
  have htrace : WordTrace (prefixWord ++ tailWord_595745) baseStart_595745 baseEnd_595745 := by
    simpa [prefixWord, tailWord_595745, baseEnd_595745] using wordTrace_append hprefix tailTrace_595745
  have hstable : (prefixWord ++ tailWord_595745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595745).length < 2 ^ (prefixWord ++ tailWord_595745).sum := by decide
  have hdescent : baseEnd_595745 < baseStart_595745 := by decide
  rcases family_descends (prefixWord ++ tailWord_595745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595764 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_595764 : Nat := 118140960795 + 595764 * 2 ^ 59
def prefixEnd_595764 : Nat := 4983230072969 + 3 ^ 40 * 595764 * 2
def baseEnd_595764 : Nat := 203942192430208202873425

theorem tailTrace_595764 : CollatzResearch.WordTrace tailWord_595764 prefixEnd_595764 203942192430208202873425 := by
  unfold tailWord_595764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864649106828125617853173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14486198809104167490470897 10864649106828125617853173)
  ·
    refine ⟨1018560853765136776673735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10864649106828125617853173 1018560853765136776673735)
    ·
      refine ⟨1527841280647705165010603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018560853765136776673735 1527841280647705165010603)
      ·
        refine ⟨2291761920971557747515905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527841280647705165010603 2291761920971557747515905)
        ·
          refine ⟨1718821440728668310636929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2291761920971557747515905 1718821440728668310636929)
          ·
            refine ⟨1289116080546501232977697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1718821440728668310636929 1289116080546501232977697)
            ·
              refine ⟨966837060409875924733273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289116080546501232977697 966837060409875924733273)
              ·
                refine ⟨725127795307406943549955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966837060409875924733273 725127795307406943549955)
                ·
                  refine ⟨1087691692961110415324933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725127795307406943549955 1087691692961110415324933)
                  ·
                    refine ⟨203942192430208202873425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087691692961110415324933 203942192430208202873425)
                    ·
                      rfl

theorem cell22_595764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_595764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595764 prefixEnd_595764 := by exact prefixLift 595764
  have htrace : WordTrace (prefixWord ++ tailWord_595764) baseStart_595764 baseEnd_595764 := by
    simpa [prefixWord, tailWord_595764, baseEnd_595764] using wordTrace_append hprefix tailTrace_595764
  have hstable : (prefixWord ++ tailWord_595764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595764).length < 2 ^ (prefixWord ++ tailWord_595764).sum := by decide
  have hdescent : baseEnd_595764 < baseStart_595764 := by decide
  rcases family_descends (prefixWord ++ tailWord_595764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595811 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 2, 3]
def baseStart_595811 : Nat := 118140960795 + 595811 * 2 ^ 59
def prefixEnd_595811 : Nat := 4983230072969 + 3 ^ 40 * 595811 * 2
def baseEnd_595811 : Nat := 203958281490715746948281

theorem tailTrace_595811 : CollatzResearch.WordTrace tailWord_595811 prefixEnd_595811 203958281490715746948281 := by
  unfold tailWord_595811
  simp only [CollatzResearch.WordTrace]
  refine ⟨21731012444485978262667287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14487341629657318841778191 21731012444485978262667287)
  ·
    refine ⟨32596518666728967394000931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21731012444485978262667287 32596518666728967394000931)
    ·
      refine ⟨48894778000093451091001397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32596518666728967394000931 48894778000093451091001397)
      ·
        refine ⟨4583885437508761039781381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48894778000093451091001397 4583885437508761039781381)
        ·
          refine ⟨859478519532892694959009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4583885437508761039781381 859478519532892694959009)
          ·
            refine ⟨644608889649669521219257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859478519532892694959009 644608889649669521219257)
            ·
              refine ⟨483456667237252140914443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644608889649669521219257 483456667237252140914443)
              ·
                refine ⟨725185000855878211371665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483456667237252140914443 725185000855878211371665)
                ·
                  refine ⟨543888750641908658528749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725185000855878211371665 543888750641908658528749)
                  ·
                    refine ⟨203958281490715746948281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 543888750641908658528749 203958281490715746948281)
                    ·
                      rfl

theorem cell22_595811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 3].length) (baseStart_595811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595811 prefixEnd_595811 := by exact prefixLift 595811
  have htrace : WordTrace (prefixWord ++ tailWord_595811) baseStart_595811 baseEnd_595811 := by
    simpa [prefixWord, tailWord_595811, baseEnd_595811] using wordTrace_append hprefix tailTrace_595811
  have hstable : (prefixWord ++ tailWord_595811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595811).length < 2 ^ (prefixWord ++ tailWord_595811).sum := by decide
  have hdescent : baseEnd_595811 < baseStart_595811 := by decide
  rcases family_descends (prefixWord ++ tailWord_595811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595865 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_595865 : Nat := 118140960795 + 595865 * 2 ^ 59
def prefixEnd_595865 : Nat := 4983230072969 + 3 ^ 40 * 595865 * 2
def baseEnd_595865 : Nat := 203976766794277606098115

theorem tailTrace_595865 : CollatzResearch.WordTrace tailWord_595865 prefixEnd_595865 203976766794277606098115 := by
  unfold tailWord_595865
  simp only [CollatzResearch.WordTrace]
  refine ⟨21732981986290345485133049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14488654657526896990088699 21732981986290345485133049)
  ·
    refine ⟨16299736489717759113849787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21732981986290345485133049 16299736489717759113849787)
    ·
      refine ⟨24449604734576638670774681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16299736489717759113849787 24449604734576638670774681)
      ·
        refine ⟨18337203550932479003081011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24449604734576638670774681 18337203550932479003081011)
        ·
          refine ⟨27505805326398718504621517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18337203550932479003081011 27505805326398718504621517)
          ·
            refine ⟨10314676997399519439233069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27505805326398718504621517 10314676997399519439233069)
            ·
              refine ⟨3868003874024819789712401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10314676997399519439233069 3868003874024819789712401)
              ·
                refine ⟨2901002905518614842284301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868003874024819789712401 2901002905518614842284301)
                ·
                  refine ⟨1087876089569480565856613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2901002905518614842284301 1087876089569480565856613)
                  ·
                    refine ⟨203976766794277606098115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087876089569480565856613 203976766794277606098115)
                    ·
                      rfl

theorem cell22_595865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_595865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595865 prefixEnd_595865 := by exact prefixLift 595865
  have htrace : WordTrace (prefixWord ++ tailWord_595865) baseStart_595865 baseEnd_595865 := by
    simpa [prefixWord, tailWord_595865, baseEnd_595865] using wordTrace_append hprefix tailTrace_595865
  have hstable : (prefixWord ++ tailWord_595865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595865).length < 2 ^ (prefixWord ++ tailWord_595865).sum := by decide
  have hdescent : baseEnd_595865 < baseStart_595865 := by decide
  rcases family_descends (prefixWord ++ tailWord_595865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595929 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_595929 : Nat := 118140960795 + 595929 * 2 ^ 59
def prefixEnd_595929 : Nat := 4983230072969 + 3 ^ 40 * 595929 * 2
def baseEnd_595929 : Nat := 203998675302202772497919

theorem tailTrace_595929 : CollatzResearch.WordTrace tailWord_595929 prefixEnd_595929 203998675302202772497919 := by
  unfold tailWord_595929
  simp only [CollatzResearch.WordTrace]
  refine ⟨21735316258058484415462841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14490210838705656276975227 21735316258058484415462841)
  ·
    refine ⟨16301487193543863311597131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21735316258058484415462841 16301487193543863311597131)
    ·
      refine ⟨24452230790315794967395697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16301487193543863311597131 24452230790315794967395697)
      ·
        refine ⟨18339173092736846225546773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24452230790315794967395697 18339173092736846225546773)
        ·
          refine ⟨859648738722039666822505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18339173092736846225546773 859648738722039666822505)
          ·
            refine ⟨644736554041529750116879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859648738722039666822505 644736554041529750116879)
            ·
              refine ⟨967104831062294625175319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644736554041529750116879 967104831062294625175319)
              ·
                refine ⟨1450657246593441937762979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967104831062294625175319 1450657246593441937762979)
                ·
                  refine ⟨2175985869890162906644469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450657246593441937762979 2175985869890162906644469)
                  ·
                    refine ⟨203998675302202772497919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2175985869890162906644469 203998675302202772497919)
                    ·
                      rfl

theorem cell22_595929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_595929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595929 prefixEnd_595929 := by exact prefixLift 595929
  have htrace : WordTrace (prefixWord ++ tailWord_595929) baseStart_595929 baseEnd_595929 := by
    simpa [prefixWord, tailWord_595929, baseEnd_595929] using wordTrace_append hprefix tailTrace_595929
  have hstable : (prefixWord ++ tailWord_595929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595929).length < 2 ^ (prefixWord ++ tailWord_595929).sum := by decide
  have hdescent : baseEnd_595929 < baseStart_595929 := by decide
  rcases family_descends (prefixWord ++ tailWord_595929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595940 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_595940 : Nat := 118140960795 + 595940 * 2 ^ 59
def prefixEnd_595940 : Nat := 4983230072969 + 3 ^ 40 * 595940 * 2
def baseEnd_595940 : Nat := 204002440827002410472885

theorem tailTrace_595940 : CollatzResearch.WordTrace tailWord_595940 prefixEnd_595940 204002440827002410472885 := by
  unfold tailWord_595940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10867858730509316647056637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14490478307345755529408849 10867858730509316647056637)
  ·
    refine ⟨4075447023940993742646239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10867858730509316647056637 4075447023940993742646239)
    ·
      refine ⟨6113170535911490613969359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075447023940993742646239 6113170535911490613969359)
      ·
        refine ⟨9169755803867235920954039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113170535911490613969359 9169755803867235920954039)
        ·
          refine ⟨13754633705800853881431059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9169755803867235920954039 13754633705800853881431059)
          ·
            refine ⟨20631950558701280822146589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13754633705800853881431059 20631950558701280822146589)
            ·
              refine ⟨7736981459512980308304971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20631950558701280822146589 7736981459512980308304971)
              ·
                refine ⟨11605472189269470462457457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7736981459512980308304971 11605472189269470462457457)
                ·
                  refine ⟨8704104141952102846843093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11605472189269470462457457 8704104141952102846843093)
                  ·
                    refine ⟨204002440827002410472885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8704104141952102846843093 204002440827002410472885)
                    ·
                      rfl

theorem cell22_595940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_595940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_595940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_595940 prefixEnd_595940 := by exact prefixLift 595940
  have htrace : WordTrace (prefixWord ++ tailWord_595940) baseStart_595940 baseEnd_595940 := by
    simpa [prefixWord, tailWord_595940, baseEnd_595940] using wordTrace_append hprefix tailTrace_595940
  have hstable : (prefixWord ++ tailWord_595940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595940).length < 2 ^ (prefixWord ++ tailWord_595940).sum := by decide
  have hdescent : baseEnd_595940 < baseStart_595940 := by decide
  rcases family_descends (prefixWord ++ tailWord_595940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596015 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 10]
def baseStart_596015 : Nat := 118140960795 + 596015 * 2 ^ 59
def prefixEnd_596015 : Nat := 4983230072969 + 3 ^ 40 * 596015 * 2
def baseEnd_596015 : Nat := 68009371619909071615885

theorem tailTrace_596015 : CollatzResearch.WordTrace tailWord_596015 prefixEnd_596015 68009371619909071615885 := by
  unfold tailWord_596015
  simp only [CollatzResearch.WordTrace]
  refine ⟨21738452935746921103093499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14492301957164614068728999 21738452935746921103093499)
  ·
    refine ⟨32607679403620381654640249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21738452935746921103093499 32607679403620381654640249)
    ·
      refine ⟨24455759552715286240980187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32607679403620381654640249 24455759552715286240980187)
      ·
        refine ⟨36683639329072929361470281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24455759552715286240980187 36683639329072929361470281)
        ·
          refine ⟨27512729496804697021102711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36683639329072929361470281 27512729496804697021102711)
          ·
            refine ⟨41269094245207045531654067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27512729496804697021102711 41269094245207045531654067)
            ·
              refine ⟨61903641367810568297481101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41269094245207045531654067 61903641367810568297481101)
              ·
                refine ⟨23213865512928963111555413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61903641367810568297481101 23213865512928963111555413)
                ·
                  refine ⟨68009371619909071615885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 23213865512928963111555413 68009371619909071615885)
                  ·
                    rfl

theorem cell22_596015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_596015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596015 prefixEnd_596015 := by exact prefixLift 596015
  have htrace : WordTrace (prefixWord ++ tailWord_596015) baseStart_596015 baseEnd_596015 := by
    simpa [prefixWord, tailWord_596015, baseEnd_596015] using wordTrace_append hprefix tailTrace_596015
  have hstable : (prefixWord ++ tailWord_596015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596015).length < 2 ^ (prefixWord ++ tailWord_596015).sum := by decide
  have hdescent : baseEnd_596015 < baseStart_596015 := by decide
  rcases family_descends (prefixWord ++ tailWord_596015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596025 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 1, 3]
def baseStart_596025 : Nat := 118140960795 + 596025 * 2 ^ 59
def prefixEnd_596025 : Nat := 4983230072969 + 3 ^ 40 * 596025 * 2
def baseEnd_596025 : Nat := 204031538064090522097625

theorem tailTrace_596025 : CollatzResearch.WordTrace tailWord_596025 prefixEnd_596025 204031538064090522097625 := by
  unfold tailWord_596025
  simp only [CollatzResearch.WordTrace]
  refine ⟨21738817665710692810957529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14492545110473795207305019 21738817665710692810957529)
  ·
    refine ⟨16304113249283019608218147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21738817665710692810957529 16304113249283019608218147)
    ·
      refine ⟨24456169873924529412327221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16304113249283019608218147 24456169873924529412327221)
      ·
        refine ⟨2292765925680424632405677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24456169873924529412327221 2292765925680424632405677)
        ·
          refine ⟨859787222130159237152129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2292765925680424632405677 859787222130159237152129)
          ·
            refine ⟨644840416597619427864097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859787222130159237152129 644840416597619427864097)
            ·
              refine ⟨483630312448214570898073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644840416597619427864097 483630312448214570898073)
              ·
                refine ⟨362722734336160928173555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483630312448214570898073 362722734336160928173555)
                ·
                  refine ⟨544084101504241392260333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362722734336160928173555 544084101504241392260333)
                  ·
                    refine ⟨204031538064090522097625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544084101504241392260333 204031538064090522097625)
                    ·
                      rfl

theorem cell22_596025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_596025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596025 prefixEnd_596025 := by exact prefixLift 596025
  have htrace : WordTrace (prefixWord ++ tailWord_596025) baseStart_596025 baseEnd_596025 := by
    simpa [prefixWord, tailWord_596025, baseEnd_596025] using wordTrace_append hprefix tailTrace_596025
  have hstable : (prefixWord ++ tailWord_596025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596025).length < 2 ^ (prefixWord ++ tailWord_596025).sum := by decide
  have hdescent : baseEnd_596025 < baseStart_596025 := by decide
  rcases family_descends (prefixWord ++ tailWord_596025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596077 : List Nat := [1, 5, 1, 1, 2, 1, 11]
def baseStart_596077 : Nat := 118140960795 + 596077 * 2 ^ 59
def prefixEnd_596077 : Nat := 4983230072969 + 3 ^ 40 * 596077 * 2
def baseEnd_596077 : Nat := 7557382915806656288795

theorem tailTrace_596077 : CollatzResearch.WordTrace tailWord_596077 prefixEnd_596077 7557382915806656288795 := by
  unfold tailWord_596077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21740714261522305691850485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14493809507681537127900323 21740714261522305691850485)
  ·
    refine ⟨2038191962017716158610983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21740714261522305691850485 2038191962017716158610983)
    ·
      refine ⟨3057287943026574237916475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038191962017716158610983 3057287943026574237916475)
      ·
        refine ⟨4585931914539861356874713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3057287943026574237916475 4585931914539861356874713)
        ·
          refine ⟨3439448935904896017656035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585931914539861356874713 3439448935904896017656035)
          ·
            refine ⟨5159173403857344026484053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439448935904896017656035 5159173403857344026484053)
            ·
              refine ⟨7557382915806656288795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5159173403857344026484053 7557382915806656288795)
              ·
                rfl

theorem cell22_596077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 11].length) (baseStart_596077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596077 prefixEnd_596077 := by exact prefixLift 596077
  have htrace : WordTrace (prefixWord ++ tailWord_596077) baseStart_596077 baseEnd_596077 := by
    simpa [prefixWord, tailWord_596077, baseEnd_596077] using wordTrace_append hprefix tailTrace_596077
  have hstable : (prefixWord ++ tailWord_596077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596077).length < 2 ^ (prefixWord ++ tailWord_596077).sum := by decide
  have hdescent : baseEnd_596077 < baseStart_596077 := by decide
  rcases family_descends (prefixWord ++ tailWord_596077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596156 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_596156 : Nat := 118140960795 + 596156 * 2 ^ 59
def prefixEnd_596156 : Nat := 4983230072969 + 3 ^ 40 * 596156 * 2
def baseEnd_596156 : Nat := 68025460680416615690741

theorem tailTrace_596156 : CollatzResearch.WordTrace tailWord_596156 prefixEnd_596156 68025460680416615690741 := by
  unfold tailWord_596156
  simp only [CollatzResearch.WordTrace]
  refine ⟨10871797814118051091988161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14495730418824068122650881 10871797814118051091988161)
  ·
    refine ⟨8153848360588538318991121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10871797814118051091988161 8153848360588538318991121)
    ·
      refine ⟨6115386270441403739243341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8153848360588538318991121 6115386270441403739243341)
      ·
        refine ⟨2293269851415526402216253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6115386270441403739243341 2293269851415526402216253)
        ·
          refine ⟨859976194280822400831095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2293269851415526402216253 859976194280822400831095)
          ·
            refine ⟨1289964291421233601246643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859976194280822400831095 1289964291421233601246643)
            ·
              refine ⟨1934946437131850401869965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289964291421233601246643 1934946437131850401869965)
              ·
                refine ⟨725604913924443900701237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1934946437131850401869965 725604913924443900701237)
                ·
                  refine ⟨68025460680416615690741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 725604913924443900701237 68025460680416615690741)
                  ·
                    rfl

theorem cell22_596156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_596156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596156 prefixEnd_596156 := by exact prefixLift 596156
  have htrace : WordTrace (prefixWord ++ tailWord_596156) baseStart_596156 baseEnd_596156 := by
    simpa [prefixWord, tailWord_596156, baseEnd_596156] using wordTrace_append hprefix tailTrace_596156
  have hstable : (prefixWord ++ tailWord_596156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596156).length < 2 ^ (prefixWord ++ tailWord_596156).sum := by decide
  have hdescent : baseEnd_596156 < baseStart_596156 := by decide
  rcases family_descends (prefixWord ++ tailWord_596156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596169 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_596169 : Nat := 118140960795 + 596169 * 2 ^ 59
def prefixEnd_596169 : Nat := 4983230072969 + 3 ^ 40 * 596169 * 2
def baseEnd_596169 : Nat := 204080832206922146497183

theorem tailTrace_596169 : CollatzResearch.WordTrace tailWord_596169 prefixEnd_596169 204080832206922146497183 := by
  unfold tailWord_596169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21744069777189005404199561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14496046518126003602799707 21744069777189005404199561)
  ·
    refine ⟨16308052332891754053149671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21744069777189005404199561 16308052332891754053149671)
    ·
      refine ⟨24462078499337631079724507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16308052332891754053149671 24462078499337631079724507)
      ·
        refine ⟨36693117749006446619586761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24462078499337631079724507 36693117749006446619586761)
        ·
          refine ⟨27519838311754834964690071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36693117749006446619586761 27519838311754834964690071)
          ·
            refine ⟨41279757467632252447035107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27519838311754834964690071 41279757467632252447035107)
            ·
              refine ⟨61919636201448378670552661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41279757467632252447035107 61919636201448378670552661)
              ·
                refine ⟨725620736735723187545539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 61919636201448378670552661 725620736735723187545539)
                ·
                  refine ⟨1088431105103584781318309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725620736735723187545539 1088431105103584781318309)
                  ·
                    refine ⟨204080832206922146497183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088431105103584781318309 204080832206922146497183)
                    ·
                      rfl

theorem cell22_596169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_596169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596169 prefixEnd_596169 := by exact prefixLift 596169
  have htrace : WordTrace (prefixWord ++ tailWord_596169) baseStart_596169 baseEnd_596169 := by
    simpa [prefixWord, tailWord_596169, baseEnd_596169] using wordTrace_append hprefix tailTrace_596169
  have hstable : (prefixWord ++ tailWord_596169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596169).length < 2 ^ (prefixWord ++ tailWord_596169).sum := by decide
  have hdescent : baseEnd_596169 < baseStart_596169 := by decide
  rcases family_descends (prefixWord ++ tailWord_596169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596194 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_596194 : Nat := 118140960795 + 596194 * 2 ^ 59
def prefixEnd_596194 : Nat := 4983230072969 + 3 ^ 40 * 596194 * 2
def baseEnd_596194 : Nat := 204089390217830414622107

theorem tailTrace_596194 : CollatzResearch.WordTrace tailWord_596194 prefixEnd_596194 204089390217830414622107 := by
  unfold tailWord_596194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436245400524608668464909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14496654401398956449239757 5436245400524608668464909)
  ·
    refine ⟨2038592025196728250674341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5436245400524608668464909 2038592025196728250674341)
    ·
      refine ⟨382236004724386547001439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2038592025196728250674341 382236004724386547001439)
      ·
        refine ⟨573354007086579820502159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382236004724386547001439 573354007086579820502159)
        ·
          refine ⟨860031010629869730753239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573354007086579820502159 860031010629869730753239)
          ·
            refine ⟨1290046515944804596129859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860031010629869730753239 1290046515944804596129859)
            ·
              refine ⟨1935069773917206894194789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290046515944804596129859 1935069773917206894194789)
              ·
                refine ⟨362825582609476292661523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1935069773917206894194789 362825582609476292661523)
                ·
                  refine ⟨544238373914214438992285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362825582609476292661523 544238373914214438992285)
                  ·
                    refine ⟨204089390217830414622107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544238373914214438992285 204089390217830414622107)
                    ·
                      rfl

theorem cell22_596194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_596194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596194 prefixEnd_596194 := by exact prefixLift 596194
  have htrace : WordTrace (prefixWord ++ tailWord_596194) baseStart_596194 baseEnd_596194 := by
    simpa [prefixWord, tailWord_596194, baseEnd_596194] using wordTrace_append hprefix tailTrace_596194
  have hstable : (prefixWord ++ tailWord_596194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596194).length < 2 ^ (prefixWord ++ tailWord_596194).sum := by decide
  have hdescent : baseEnd_596194 < baseStart_596194 := by decide
  rcases family_descends (prefixWord ++ tailWord_596194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596250 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_596250 : Nat := 118140960795 + 596250 * 2 ^ 59
def prefixEnd_596250 : Nat := 4983230072969 + 3 ^ 40 * 596250 * 2
def baseEnd_596250 : Nat := 204108560162264935221935

theorem tailTrace_596250 : CollatzResearch.WordTrace tailWord_596250 prefixEnd_596250 204108560162264935221935 := by
  unfold tailWord_596250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436756022473889059474551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14498016059930370825265469 5436756022473889059474551)
  ·
    refine ⟨8155134033710833589211827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5436756022473889059474551 8155134033710833589211827)
    ·
      refine ⟨12232701050566250383817741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8155134033710833589211827 12232701050566250383817741)
      ·
        refine ⟨4587262893962343893931653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12232701050566250383817741 4587262893962343893931653)
        ·
          refine ⟨860111792617939480112185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4587262893962343893931653 860111792617939480112185)
          ·
            refine ⟨645083844463454610084139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860111792617939480112185 645083844463454610084139)
            ·
              refine ⟨967625766695181915126209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645083844463454610084139 967625766695181915126209)
              ·
                refine ⟨725719325021386436344657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967625766695181915126209 725719325021386436344657)
                ·
                  refine ⟨544289493766039827258493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725719325021386436344657 544289493766039827258493)
                  ·
                    refine ⟨204108560162264935221935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544289493766039827258493 204108560162264935221935)
                    ·
                      rfl

theorem cell22_596250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_596250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596250 prefixEnd_596250 := by exact prefixLift 596250
  have htrace : WordTrace (prefixWord ++ tailWord_596250) baseStart_596250 baseEnd_596250 := by
    simpa [prefixWord, tailWord_596250, baseEnd_596250] using wordTrace_append hprefix tailTrace_596250
  have hstable : (prefixWord ++ tailWord_596250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596250).length < 2 ^ (prefixWord ++ tailWord_596250).sum := by decide
  have hdescent : baseEnd_596250 < baseStart_596250 := by decide
  rcases family_descends (prefixWord ++ tailWord_596250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596318 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_596318 : Nat := 118140960795 + 596318 * 2 ^ 59
def prefixEnd_596318 : Nat := 4983230072969 + 3 ^ 40 * 596318 * 2
def baseEnd_596318 : Nat := 204131837951935424521727

theorem tailTrace_596318 : CollatzResearch.WordTrace tailWord_596318 prefixEnd_596318 204131837951935424521727 := by
  unfold tailWord_596318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718688031706150481421701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14499669502432802567582405 2718688031706150481421701)
  ·
    refine ⟨509754005944903215266569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2718688031706150481421701 509754005944903215266569)
    ·
      refine ⟨382315504458677411449927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 509754005944903215266569 382315504458677411449927)
      ·
        refine ⟨573473256688016117174891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382315504458677411449927 573473256688016117174891)
        ·
          refine ⟨860209885032024175762337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573473256688016117174891 860209885032024175762337)
          ·
            refine ⟨645157413774018131821753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860209885032024175762337 645157413774018131821753)
            ·
              refine ⟨483868060330513598866315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645157413774018131821753 483868060330513598866315)
              ·
                refine ⟨725802090495770398299473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483868060330513598866315 725802090495770398299473)
                ·
                  refine ⟨544351567871827798724605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725802090495770398299473 544351567871827798724605)
                  ·
                    refine ⟨204131837951935424521727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544351567871827798724605 204131837951935424521727)
                    ·
                      rfl

theorem cell22_596318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_596318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596318 prefixEnd_596318 := by exact prefixLift 596318
  have htrace : WordTrace (prefixWord ++ tailWord_596318) baseStart_596318 baseEnd_596318 := by
    simpa [prefixWord, tailWord_596318, baseEnd_596318] using wordTrace_append hprefix tailTrace_596318
  have hstable : (prefixWord ++ tailWord_596318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596318).length < 2 ^ (prefixWord ++ tailWord_596318).sum := by decide
  have hdescent : baseEnd_596318 < baseStart_596318 := by decide
  rcases family_descends (prefixWord ++ tailWord_596318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596338 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_596338 : Nat := 118140960795 + 596338 * 2 ^ 59
def prefixEnd_596338 : Nat := 4983230072969 + 3 ^ 40 * 596338 * 2
def baseEnd_596338 : Nat := 204138684360662039021665

theorem tailTrace_596338 : CollatzResearch.WordTrace tailWord_596338 prefixEnd_596338 204138684360662039021665 := by
  unfold tailWord_596338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437558428394186816775417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14500155809051164844734445 5437558428394186816775417)
  ·
    refine ⟨4078168821295640112581563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5437558428394186816775417 4078168821295640112581563)
    ·
      refine ⟨6117253231943460168872345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078168821295640112581563 6117253231943460168872345)
      ·
        refine ⟨4587939923957595126654259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6117253231943460168872345 4587939923957595126654259)
        ·
          refine ⟨6881909885936392689981389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587939923957595126654259 6881909885936392689981389)
          ·
            refine ⟨2580716207226147258743021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6881909885936392689981389 2580716207226147258743021)
            ·
              refine ⟨967768577709805222028633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2580716207226147258743021 967768577709805222028633)
              ·
                refine ⟨725826433282353916521475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967768577709805222028633 725826433282353916521475)
                ·
                  refine ⟨1088739649923530874782213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725826433282353916521475 1088739649923530874782213)
                  ·
                    refine ⟨204138684360662039021665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088739649923530874782213 204138684360662039021665)
                    ·
                      rfl

theorem cell22_596338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_596338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596338 prefixEnd_596338 := by exact prefixLift 596338
  have htrace : WordTrace (prefixWord ++ tailWord_596338) baseStart_596338 baseEnd_596338 := by
    simpa [prefixWord, tailWord_596338, baseEnd_596338] using wordTrace_append hprefix tailTrace_596338
  have hstable : (prefixWord ++ tailWord_596338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596338).length < 2 ^ (prefixWord ++ tailWord_596338).sum := by decide
  have hdescent : baseEnd_596338 < baseStart_596338 := by decide
  rcases family_descends (prefixWord ++ tailWord_596338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596355 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 1, 4]
def baseStart_596355 : Nat := 118140960795 + 596355 * 2 ^ 59
def prefixEnd_596355 : Nat := 4983230072969 + 3 ^ 40 * 596355 * 2
def baseEnd_596355 : Nat := 204144503808079661346613

theorem tailTrace_596355 : CollatzResearch.WordTrace tailWord_596355 prefixEnd_596355 204144503808079661346613 := by
  unfold tailWord_596355
  simp only [CollatzResearch.WordTrace]
  refine ⟨21750853754515159170470519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14500569169676772780313679 21750853754515159170470519)
  ·
    refine ⟨32626280631772738755705779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21750853754515159170470519 32626280631772738755705779)
    ·
      refine ⟨48939420947659108133558669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32626280631772738755705779 48939420947659108133558669)
      ·
        refine ⟨18352282855372165550084501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48939420947659108133558669 18352282855372165550084501)
        ·
          refine ⟨860263258845570260160211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18352282855372165550084501 860263258845570260160211)
          ·
            refine ⟨1290394888268355390240317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860263258845570260160211 1290394888268355390240317)
            ·
              refine ⟨483898083100633271340119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1290394888268355390240317 483898083100633271340119)
              ·
                refine ⟨725847124650949907010179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483898083100633271340119 725847124650949907010179)
                ·
                  refine ⟨1088770686976424860515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725847124650949907010179 1088770686976424860515269)
                  ·
                    refine ⟨204144503808079661346613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088770686976424860515269 204144503808079661346613)
                    ·
                      rfl

theorem cell22_596355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 4].length) (baseStart_596355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596355 prefixEnd_596355 := by exact prefixLift 596355
  have htrace : WordTrace (prefixWord ++ tailWord_596355) baseStart_596355 baseEnd_596355 := by
    simpa [prefixWord, tailWord_596355, baseEnd_596355] using wordTrace_append hprefix tailTrace_596355
  have hstable : (prefixWord ++ tailWord_596355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596355).length < 2 ^ (prefixWord ++ tailWord_596355).sum := by decide
  have hdescent : baseEnd_596355 < baseStart_596355 := by decide
  rcases family_descends (prefixWord ++ tailWord_596355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596364 : List Nat := [2, 2, 1, 2, 1, 14]
def baseStart_596364 : Nat := 118140960795 + 596364 * 2 ^ 59
def prefixEnd_596364 : Nat := 4983230072969 + 3 ^ 40 * 596364 * 2
def baseEnd_596364 : Nat := 2520340551753168368785

theorem tailTrace_596364 : CollatzResearch.WordTrace tailWord_596364 prefixEnd_596364 2520340551753168368785 := by
  unfold tailWord_596364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10875591005741276853774073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14500788007655035805032097 10875591005741276853774073)
  ·
    refine ⟨8156693254305957640330555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10875591005741276853774073 8156693254305957640330555)
    ·
      refine ⟨12235039881458936460495833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8156693254305957640330555 12235039881458936460495833)
      ·
        refine ⟨9176279911094202345371875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12235039881458936460495833 9176279911094202345371875)
        ·
          refine ⟨13764419866641303518057813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9176279911094202345371875 13764419866641303518057813)
          ·
            refine ⟨2520340551753168368785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 13764419866641303518057813 2520340551753168368785)
            ·
              rfl

theorem cell22_596364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 14].length) (baseStart_596364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596364 prefixEnd_596364 := by exact prefixLift 596364
  have htrace : WordTrace (prefixWord ++ tailWord_596364) baseStart_596364 baseEnd_596364 := by
    simpa [prefixWord, tailWord_596364, baseEnd_596364] using wordTrace_append hprefix tailTrace_596364
  have hstable : (prefixWord ++ tailWord_596364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596364).length < 2 ^ (prefixWord ++ tailWord_596364).sum := by decide
  have hdescent : baseEnd_596364 < baseStart_596364 := by decide
  rcases family_descends (prefixWord ++ tailWord_596364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596385 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_596385 : Nat := 118140960795 + 596385 * 2 ^ 59
def prefixEnd_596385 : Nat := 4983230072969 + 3 ^ 40 * 596385 * 2
def baseEnd_596385 : Nat := 204154773421169583096521

theorem tailTrace_596385 : CollatzResearch.WordTrace tailWord_596385 prefixEnd_596385 204154773421169583096521 := by
  unfold tailWord_596385
  simp only [CollatzResearch.WordTrace]
  refine ⟨21751947944406474294062609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14501298629604316196041739 21751947944406474294062609)
  ·
    refine ⟨16313960958304855720546957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21751947944406474294062609 16313960958304855720546957)
    ·
      refine ⟨6117735359364320895205109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16313960958304855720546957 6117735359364320895205109)
      ·
        refine ⟨573537689940405083925479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6117735359364320895205109 573537689940405083925479)
        ·
          refine ⟨860306534910607625888219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573537689940405083925479 860306534910607625888219)
          ·
            refine ⟨1290459802365911438832329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860306534910607625888219 1290459802365911438832329)
            ·
              refine ⟨967844851774433579124247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290459802365911438832329 967844851774433579124247)
              ·
                refine ⟨1451767277661650368686371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967844851774433579124247 1451767277661650368686371)
                ·
                  refine ⟨2177650916492475553029557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451767277661650368686371 2177650916492475553029557)
                  ·
                    refine ⟨204154773421169583096521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2177650916492475553029557 204154773421169583096521)
                    ·
                      rfl

theorem cell22_596385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_596385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596385 prefixEnd_596385 := by exact prefixLift 596385
  have htrace : WordTrace (prefixWord ++ tailWord_596385) baseStart_596385 baseEnd_596385 := by
    simpa [prefixWord, tailWord_596385, baseEnd_596385] using wordTrace_append hprefix tailTrace_596385
  have hstable : (prefixWord ++ tailWord_596385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596385).length < 2 ^ (prefixWord ++ tailWord_596385).sum := by decide
  have hdescent : baseEnd_596385 < baseStart_596385 := by decide
  rcases family_descends (prefixWord ++ tailWord_596385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596404 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 4]
def baseStart_596404 : Nat := 118140960795 + 596404 * 2 ^ 59
def prefixEnd_596404 : Nat := 4983230072969 + 3 ^ 40 * 596404 * 2
def baseEnd_596404 : Nat := 68053759169819955623821

theorem tailTrace_596404 : CollatzResearch.WordTrace tailWord_596404 prefixEnd_596404 68053759169819955623821 := by
  unfold tailWord_596404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876320465668820269502133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14501760620891760359336177 10876320465668820269502133)
  ·
    refine ⟨1019655043656451900265825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10876320465668820269502133 1019655043656451900265825)
    ·
      refine ⟨764741282742338925199369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1019655043656451900265825 764741282742338925199369)
      ·
        refine ⟨573555962056754193899527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 764741282742338925199369 573555962056754193899527)
        ·
          refine ⟨860333943085131290849291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573555962056754193899527 860333943085131290849291)
          ·
            refine ⟨1290500914627696936273937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860333943085131290849291 1290500914627696936273937)
            ·
              refine ⟨967875685970772702205453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290500914627696936273937 967875685970772702205453)
              ·
                refine ⟨362953382239039763327045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 967875685970772702205453 362953382239039763327045)
                ·
                  refine ⟨68053759169819955623821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 362953382239039763327045 68053759169819955623821)
                  ·
                    rfl

theorem cell22_596404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_596404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596404 prefixEnd_596404 := by exact prefixLift 596404
  have htrace : WordTrace (prefixWord ++ tailWord_596404) baseStart_596404 baseEnd_596404 := by
    simpa [prefixWord, tailWord_596404, baseEnd_596404] using wordTrace_append hprefix tailTrace_596404
  have hstable : (prefixWord ++ tailWord_596404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596404).length < 2 ^ (prefixWord ++ tailWord_596404).sum := by decide
  have hdescent : baseEnd_596404 < baseStart_596404 := by decide
  rcases family_descends (prefixWord ++ tailWord_596404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596426 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_596426 : Nat := 118140960795 + 596426 * 2 ^ 59
def prefixEnd_596426 : Nat := 4983230072969 + 3 ^ 40 * 596426 * 2
def baseEnd_596426 : Nat := 68056269519686380940465

theorem tailTrace_596426 : CollatzResearch.WordTrace tailWord_596426 prefixEnd_596426 68056269519686380940465 := by
  unfold tailWord_596426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438360834314484574076283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14502295558171958864203421 5438360834314484574076283)
  ·
    refine ⟨8157541251471726861114425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5438360834314484574076283 8157541251471726861114425)
    ·
      refine ⟨6118155938603795145835819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8157541251471726861114425 6118155938603795145835819)
      ·
        refine ⟨9177233907905692718753729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6118155938603795145835819 9177233907905692718753729)
        ·
          refine ⟨6882925430929269539065297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9177233907905692718753729 6882925430929269539065297)
          ·
            refine ⟨5162194073196952154298973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6882925430929269539065297 5162194073196952154298973)
            ·
              refine ⟨1935822777448857057862115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5162194073196952154298973 1935822777448857057862115)
              ·
                refine ⟨2903734166173285586793173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935822777448857057862115 2903734166173285586793173)
                ·
                  refine ⟨68056269519686380940465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2903734166173285586793173 68056269519686380940465)
                  ·
                    rfl

theorem cell22_596426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_596426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596426 prefixEnd_596426 := by exact prefixLift 596426
  have htrace : WordTrace (prefixWord ++ tailWord_596426) baseStart_596426 baseEnd_596426 := by
    simpa [prefixWord, tailWord_596426, baseEnd_596426] using wordTrace_append hprefix tailTrace_596426
  have hstable : (prefixWord ++ tailWord_596426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596426).length < 2 ^ (prefixWord ++ tailWord_596426).sum := by decide
  have hdescent : baseEnd_596426 < baseStart_596426 := by decide
  rcases family_descends (prefixWord ++ tailWord_596426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596441 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_596441 : Nat := 118140960795 + 596441 * 2 ^ 59
def prefixEnd_596441 : Nat := 4983230072969 + 3 ^ 40 * 596441 * 2
def baseEnd_596441 : Nat := 204173943365604103696349

theorem tailTrace_596441 : CollatzResearch.WordTrace tailWord_596441 prefixEnd_596441 204173943365604103696349 := by
  unfold tailWord_596441
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753990432203595858101177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14502660288135730572067451 21753990432203595858101177)
  ·
    refine ⟨16315492824152696893575883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21753990432203595858101177 16315492824152696893575883)
    ·
      refine ⟨24473239236229045340363825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16315492824152696893575883 24473239236229045340363825)
      ·
        refine ⟨18354929427171784005272869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24473239236229045340363825 18354929427171784005272869)
        ·
          refine ⟨3441549267594709500988663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18354929427171784005272869 3441549267594709500988663)
          ·
            refine ⟨5162323901392064251482995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441549267594709500988663 5162323901392064251482995)
            ·
              refine ⟨7743485852088096377224493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162323901392064251482995 7743485852088096377224493)
              ·
                refine ⟨2903807194533036141459185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7743485852088096377224493 2903807194533036141459185)
                ·
                  refine ⟨2177855395899777106094389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2903807194533036141459185 2177855395899777106094389)
                  ·
                    refine ⟨204173943365604103696349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2177855395899777106094389 204173943365604103696349)
                    ·
                      rfl

theorem cell22_596441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_596441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596441 prefixEnd_596441 := by exact prefixLift 596441
  have htrace : WordTrace (prefixWord ++ tailWord_596441) baseStart_596441 baseEnd_596441 := by
    simpa [prefixWord, tailWord_596441, baseEnd_596441] using wordTrace_append hprefix tailTrace_596441
  have hstable : (prefixWord ++ tailWord_596441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596441).length < 2 ^ (prefixWord ++ tailWord_596441).sum := by decide
  have hdescent : baseEnd_596441 < baseStart_596441 := by decide
  rcases family_descends (prefixWord ++ tailWord_596441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596473 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_596473 : Nat := 118140960795 + 596473 * 2 ^ 59
def prefixEnd_596473 : Nat := 4983230072969 + 3 ^ 40 * 596473 * 2
def baseEnd_596473 : Nat := 204184897619566686896251

theorem tailTrace_596473 : CollatzResearch.WordTrace tailWord_596473 prefixEnd_596473 204184897619566686896251 := by
  unfold tailWord_596473
  simp only [CollatzResearch.WordTrace]
  refine ⟨21755157568087665323266073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14503438378725110215510715 21755157568087665323266073)
  ·
    refine ⟨16316368176065748992449555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21755157568087665323266073 16316368176065748992449555)
    ·
      refine ⟨24474552264098623488674333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16316368176065748992449555 24474552264098623488674333)
      ·
        refine ⟨9177957099036983808252875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24474552264098623488674333 9177957099036983808252875)
        ·
          refine ⟨13766935648555475712379313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177957099036983808252875 13766935648555475712379313)
          ·
            refine ⟨10325201736416606784284485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13766935648555475712379313 10325201736416606784284485)
            ·
              refine ⟨1935975325578113772053341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10325201736416606784284485 1935975325578113772053341)
              ·
                refine ⟨725990747091792664520003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1935975325578113772053341 725990747091792664520003)
                ·
                  refine ⟨1088986120637688996780005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725990747091792664520003 1088986120637688996780005)
                  ·
                    refine ⟨204184897619566686896251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088986120637688996780005 204184897619566686896251)
                    ·
                      rfl

theorem cell22_596473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_596473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596473 prefixEnd_596473 := by exact prefixLift 596473
  have htrace : WordTrace (prefixWord ++ tailWord_596473) baseStart_596473 baseEnd_596473 := by
    simpa [prefixWord, tailWord_596473, baseEnd_596473] using wordTrace_append hprefix tailTrace_596473
  have hstable : (prefixWord ++ tailWord_596473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596473).length < 2 ^ (prefixWord ++ tailWord_596473).sum := by decide
  have hdescent : baseEnd_596473 < baseStart_596473 := by decide
  rcases family_descends (prefixWord ++ tailWord_596473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596520 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_596520 : Nat := 118140960795 + 596520 * 2 ^ 59
def prefixEnd_596520 : Nat := 4983230072969 + 3 ^ 40 * 596520 * 2
def baseEnd_596520 : Nat := 204200986680074230971107

theorem tailTrace_596520 : CollatzResearch.WordTrace tailWord_596520 prefixEnd_596520 204200986680074230971107 := by
  unfold tailWord_596520
  simp only [CollatzResearch.WordTrace]
  refine ⟨10878435899458696175113507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14504581199278261566818009 10878435899458696175113507)
  ·
    refine ⟨16317653849188044262670261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10878435899458696175113507 16317653849188044262670261)
    ·
      refine ⟨1529780048361379149625337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16317653849188044262670261 1529780048361379149625337)
      ·
        refine ⟨1147335036271034362219003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1529780048361379149625337 1147335036271034362219003)
        ·
          refine ⟨1721002554406551543328505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147335036271034362219003 1721002554406551543328505)
          ·
            refine ⟨1290751915804913657496379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721002554406551543328505 1290751915804913657496379)
            ·
              refine ⟨1936127873707370486244569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290751915804913657496379 1936127873707370486244569)
              ·
                refine ⟨1452095905280527864683427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936127873707370486244569 1452095905280527864683427)
                ·
                  refine ⟨2178143857920791797025141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452095905280527864683427 2178143857920791797025141)
                  ·
                    refine ⟨204200986680074230971107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2178143857920791797025141 204200986680074230971107)
                    ·
                      rfl

theorem cell22_596520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_596520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596520 prefixEnd_596520 := by exact prefixLift 596520
  have htrace : WordTrace (prefixWord ++ tailWord_596520) baseStart_596520 baseEnd_596520 := by
    simpa [prefixWord, tailWord_596520, baseEnd_596520] using wordTrace_append hprefix tailTrace_596520
  have hstable : (prefixWord ++ tailWord_596520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596520).length < 2 ^ (prefixWord ++ tailWord_596520).sum := by decide
  have hdescent : baseEnd_596520 < baseStart_596520 := by decide
  rcases family_descends (prefixWord ++ tailWord_596520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596612 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 5]
def baseStart_596612 : Nat := 118140960795 + 596612 * 2 ^ 59
def prefixEnd_596612 : Nat := 4983230072969 + 3 ^ 40 * 596612 * 2
def baseEnd_596612 : Nat := 68077493386738885890275

theorem tailTrace_596612 : CollatzResearch.WordTrace tailWord_596612 prefixEnd_596612 68077493386738885890275 := by
  unfold tailWord_596612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880113657292046031288045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14506818209722728041717393 10880113657292046031288045)
  ·
    refine ⟨4080042621484517261733017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10880113657292046031288045 4080042621484517261733017)
    ·
      refine ⟨3060031966113387946299763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4080042621484517261733017 3060031966113387946299763)
      ·
        refine ⟨4590047949170081919449645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060031966113387946299763 4590047949170081919449645)
        ·
          refine ⟨1721267980938780719793617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4590047949170081919449645 1721267980938780719793617)
          ·
            refine ⟨1290950985704085539845213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721267980938780719793617 1290950985704085539845213)
            ·
              refine ⟨484106619639032077441955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1290950985704085539845213 484106619639032077441955)
              ·
                refine ⟨726159929458548116162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484106619639032077441955 726159929458548116162933)
                ·
                  refine ⟨68077493386738885890275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726159929458548116162933 68077493386738885890275)
                  ·
                    rfl

theorem cell22_596612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_596612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596612 prefixEnd_596612 := by exact prefixLift 596612
  have htrace : WordTrace (prefixWord ++ tailWord_596612) baseStart_596612 baseEnd_596612 := by
    simpa [prefixWord, tailWord_596612, baseEnd_596612] using wordTrace_append hprefix tailTrace_596612
  have hstable : (prefixWord ++ tailWord_596612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596612).length < 2 ^ (prefixWord ++ tailWord_596612).sum := by decide
  have hdescent : baseEnd_596612 < baseStart_596612 := by decide
  rcases family_descends (prefixWord ++ tailWord_596612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596655 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 4, 3]
def baseStart_596655 : Nat := 118140960795 + 596655 * 2 ^ 59
def prefixEnd_596655 : Nat := 4983230072969 + 3 ^ 40 * 596655 * 2
def baseEnd_596655 : Nat := 204247199938978878845693

theorem tailTrace_596655 : CollatzResearch.WordTrace tailWord_596655 prefixEnd_596655 204247199938978878845693 := by
  unfold tailWord_596655
  simp only [CollatzResearch.WordTrace]
  refine ⟨21761795653428310406391419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14507863768952206937594279 21761795653428310406391419)
  ·
    refine ⟨32642693480142465609587129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21761795653428310406391419 32642693480142465609587129)
    ·
      refine ⟨24482020110106849207190347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32642693480142465609587129 24482020110106849207190347)
      ·
        refine ⟨36723030165160273810785521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24482020110106849207190347 36723030165160273810785521)
        ·
          refine ⟨27542272623870205358089141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36723030165160273810785521 27542272623870205358089141)
          ·
            refine ⟨2582088058487831752320857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27542272623870205358089141 2582088058487831752320857)
            ·
              refine ⟨1936566043865873814240643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582088058487831752320857 1936566043865873814240643)
              ·
                refine ⟨2904849065798810721360965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936566043865873814240643 2904849065798810721360965)
                ·
                  refine ⟨544659199837277010255181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2904849065798810721360965 544659199837277010255181)
                  ·
                    refine ⟨204247199938978878845693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544659199837277010255181 204247199938978878845693)
                    ·
                      rfl

theorem cell22_596655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_596655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596655 prefixEnd_596655 := by exact prefixLift 596655
  have htrace : WordTrace (prefixWord ++ tailWord_596655) baseStart_596655 baseEnd_596655 := by
    simpa [prefixWord, tailWord_596655, baseEnd_596655] using wordTrace_append hprefix tailTrace_596655
  have hstable : (prefixWord ++ tailWord_596655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596655).length < 2 ^ (prefixWord ++ tailWord_596655).sum := by decide
  have hdescent : baseEnd_596655 < baseStart_596655 := by decide
  rcases family_descends (prefixWord ++ tailWord_596655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596670 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_596670 : Nat := 118140960795 + 596670 * 2 ^ 59
def prefixEnd_596670 : Nat := 4983230072969 + 3 ^ 40 * 596670 * 2
def baseEnd_596670 : Nat := 204252334745523839720647

theorem tailTrace_596670 : CollatzResearch.WordTrace tailWord_596670 prefixEnd_596670 204252334745523839720647 := by
  unfold tailWord_596670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720292843546745996023433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14508228498915978645458309 2720292843546745996023433)
  ·
    refine ⟨2040219632660059497017575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2720292843546745996023433 2040219632660059497017575)
    ·
      refine ⟨3060329448990089245526363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040219632660059497017575 3060329448990089245526363)
      ·
        refine ⟨4590494173485133868289545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060329448990089245526363 4590494173485133868289545)
        ·
          refine ⟨3442870630113850401217159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4590494173485133868289545 3442870630113850401217159)
          ·
            refine ⟨5164305945170775601825739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442870630113850401217159 5164305945170775601825739)
            ·
              refine ⟨7746458917756163402738609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164305945170775601825739 7746458917756163402738609)
              ·
                refine ⟨5809844188317122552053957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7746458917756163402738609 5809844188317122552053957)
                ·
                  refine ⟨1089345785309460478510117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5809844188317122552053957 1089345785309460478510117)
                  ·
                    refine ⟨204252334745523839720647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1089345785309460478510117 204252334745523839720647)
                    ·
                      rfl

theorem cell22_596670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_596670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596670 prefixEnd_596670 := by exact prefixLift 596670
  have htrace : WordTrace (prefixWord ++ tailWord_596670) baseStart_596670 baseEnd_596670 := by
    simpa [prefixWord, tailWord_596670, baseEnd_596670] using wordTrace_append hprefix tailTrace_596670
  have hstable : (prefixWord ++ tailWord_596670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596670).length < 2 ^ (prefixWord ++ tailWord_596670).sum := by decide
  have hdescent : baseEnd_596670 < baseStart_596670 := by decide
  rcases family_descends (prefixWord ++ tailWord_596670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596672 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_596672 : Nat := 118140960795 + 596672 * 2 ^ 59
def prefixEnd_596672 : Nat := 4983230072969 + 3 ^ 40 * 596672 * 2
def baseEnd_596672 : Nat := 204253019386396501170641

theorem tailTrace_596672 : CollatzResearch.WordTrace tailWord_596672 prefixEnd_596672 204253019386396501170641 := by
  unfold tailWord_596672
  simp only [CollatzResearch.WordTrace]
  refine ⟨10881207847183361154880135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14508277129577814873173513 10881207847183361154880135)
  ·
    refine ⟨16321811770775041732320203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10881207847183361154880135 16321811770775041732320203)
    ·
      refine ⟨24482717656162562598480305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16321811770775041732320203 24482717656162562598480305)
      ·
        refine ⟨18362038242121921948860229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24482717656162562598480305 18362038242121921948860229)
        ·
          refine ⟨3442882170397860365411293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18362038242121921948860229 3442882170397860365411293)
          ·
            refine ⟨1291080813899197637029235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3442882170397860365411293 1291080813899197637029235)
            ·
              refine ⟨1936621220848796455543853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291080813899197637029235 1936621220848796455543853)
              ·
                refine ⟨726232957818298670828945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1936621220848796455543853 726232957818298670828945)
                ·
                  refine ⟨544674718363724003121709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 726232957818298670828945 544674718363724003121709)
                  ·
                    refine ⟨204253019386396501170641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544674718363724003121709 204253019386396501170641)
                    ·
                      rfl

theorem cell22_596672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_596672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596672 prefixEnd_596672 := by exact prefixLift 596672
  have htrace : WordTrace (prefixWord ++ tailWord_596672) baseStart_596672 baseEnd_596672 := by
    simpa [prefixWord, tailWord_596672, baseEnd_596672] using wordTrace_append hprefix tailTrace_596672
  have hstable : (prefixWord ++ tailWord_596672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596672).length < 2 ^ (prefixWord ++ tailWord_596672).sum := by decide
  have hdescent : baseEnd_596672 < baseStart_596672 := by decide
  rcases family_descends (prefixWord ++ tailWord_596672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596713 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 7]
def baseStart_596713 : Nat := 118140960795 + 596713 * 2 ^ 59
def prefixEnd_596713 : Nat := 4983230072969 + 3 ^ 40 * 596713 * 2
def baseEnd_596713 : Nat := 68089018174762020298505

theorem tailTrace_596713 : CollatzResearch.WordTrace tailWord_596713 prefixEnd_596713 68089018174762020298505 := by
  unfold tailWord_596713
  simp only [CollatzResearch.WordTrace]
  refine ⟨21763911087218186312002793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14509274058145457541335195 21763911087218186312002793)
  ·
    refine ⟨16322933315413639734002095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21763911087218186312002793 16322933315413639734002095)
    ·
      refine ⟨24484399973120459601003143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16322933315413639734002095 24484399973120459601003143)
      ·
        refine ⟨36726599959680689401504715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24484399973120459601003143 36726599959680689401504715)
        ·
          refine ⟨55089899939521034102257073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36726599959680689401504715 55089899939521034102257073)
          ·
            refine ⟨41317424954640775576692805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55089899939521034102257073 41317424954640775576692805)
            ·
              refine ⟨7747017178995145420629901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41317424954640775576692805 7747017178995145420629901)
              ·
                refine ⟨2905131442123179532736213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7747017178995145420629901 2905131442123179532736213)
                ·
                  refine ⟨68089018174762020298505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2905131442123179532736213 68089018174762020298505)
                  ·
                    rfl

theorem cell22_596713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_596713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596713 prefixEnd_596713 := by exact prefixLift 596713
  have htrace : WordTrace (prefixWord ++ tailWord_596713) baseStart_596713 baseEnd_596713 := by
    simpa [prefixWord, tailWord_596713, baseEnd_596713] using wordTrace_append hprefix tailTrace_596713
  have hstable : (prefixWord ++ tailWord_596713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596713).length < 2 ^ (prefixWord ++ tailWord_596713).sum := by decide
  have hdescent : baseEnd_596713 < baseStart_596713 := by decide
  rcases family_descends (prefixWord ++ tailWord_596713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596717 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_596717 : Nat := 118140960795 + 596717 * 2 ^ 59
def prefixEnd_596717 : Nat := 4983230072969 + 3 ^ 40 * 596717 * 2
def baseEnd_596717 : Nat := 204268423806031383795503

theorem tailTrace_596717 : CollatzResearch.WordTrace tailWord_596717 prefixEnd_596717 204268423806031383795503 := by
  unfold tailWord_596717
  simp only [CollatzResearch.WordTrace]
  refine ⟨21764056979203694995148405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14509371319469129996765603 21764056979203694995148405)
  ·
    refine ⟨2040380341800346405795163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21764056979203694995148405 2040380341800346405795163)
    ·
      refine ⟨3060570512700519608692745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040380341800346405795163 3060570512700519608692745)
      ·
        refine ⟨2295427884525389706519559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3060570512700519608692745 2295427884525389706519559)
        ·
          refine ⟨3443141826788084559779339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295427884525389706519559 3443141826788084559779339)
          ·
            refine ⟨5164712740182126839669009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443141826788084559779339 5164712740182126839669009)
            ·
              refine ⟨3873534555136595129751757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5164712740182126839669009 3873534555136595129751757)
              ·
                refine ⟨1452575458176223173656909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3873534555136595129751757 1452575458176223173656909)
                ·
                  refine ⟨544715796816083690121341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1452575458176223173656909 544715796816083690121341)
                  ·
                    refine ⟨204268423806031383795503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544715796816083690121341 204268423806031383795503)
                    ·
                      rfl

theorem cell22_596717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_596717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596717 prefixEnd_596717 := by exact prefixLift 596717
  have htrace : WordTrace (prefixWord ++ tailWord_596717) baseStart_596717 baseEnd_596717 := by
    simpa [prefixWord, tailWord_596717, baseEnd_596717] using wordTrace_append hprefix tailTrace_596717
  have hstable : (prefixWord ++ tailWord_596717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596717).length < 2 ^ (prefixWord ++ tailWord_596717).sum := by decide
  have hdescent : baseEnd_596717 < baseStart_596717 := by decide
  rcases family_descends (prefixWord ++ tailWord_596717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596730 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_596730 : Nat := 118140960795 + 596730 * 2 ^ 59
def prefixEnd_596730 : Nat := 4983230072969 + 3 ^ 40 * 596730 * 2
def baseEnd_596730 : Nat := 68090957990567894406821

theorem tailTrace_596730 : CollatzResearch.WordTrace tailWord_596730 prefixEnd_596730 68090957990567894406821 := by
  unfold tailWord_596730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441132782039149553842911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14509687418771065476914429 5441132782039149553842911)
  ·
    refine ⟨8161699173058724330764367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441132782039149553842911 8161699173058724330764367)
    ·
      refine ⟨12242548759588086496146551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8161699173058724330764367 12242548759588086496146551)
      ·
        refine ⟨18363823139382129744219827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12242548759588086496146551 18363823139382129744219827)
        ·
          refine ⟨27545734709073194616329741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18363823139382129744219827 27545734709073194616329741)
          ·
            refine ⟨10329650515902447981123653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27545734709073194616329741 10329650515902447981123653)
            ·
              refine ⟨1936809471731708996460685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10329650515902447981123653 1936809471731708996460685)
              ·
                refine ⟨726303551899390873672757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1936809471731708996460685 726303551899390873672757)
                ·
                  refine ⟨68090957990567894406821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726303551899390873672757 68090957990567894406821)
                  ·
                    rfl

theorem cell22_596730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_596730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596730 prefixEnd_596730 := by exact prefixLift 596730
  have htrace : WordTrace (prefixWord ++ tailWord_596730) baseStart_596730 baseEnd_596730 := by
    simpa [prefixWord, tailWord_596730, baseEnd_596730] using wordTrace_append hprefix tailTrace_596730
  have hstable : (prefixWord ++ tailWord_596730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596730).length < 2 ^ (prefixWord ++ tailWord_596730).sum := by decide
  have hdescent : baseEnd_596730 < baseStart_596730 := by decide
  rcases family_descends (prefixWord ++ tailWord_596730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596734 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_596734 : Nat := 118140960795 + 596734 * 2 ^ 59
def prefixEnd_596734 : Nat := 4983230072969 + 3 ^ 40 * 596734 * 2
def baseEnd_596734 : Nat := 204274243253449006120451

theorem tailTrace_596734 : CollatzResearch.WordTrace tailWord_596734 prefixEnd_596734 204274243253449006120451 := by
  unfold tailWord_596734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720584627517763362314657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14509784680094737932344837 2720584627517763362314657)
  ·
    refine ⟨2040438470638322521735993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2720584627517763362314657 2040438470638322521735993)
    ·
      refine ⟨1530328852978741891301995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2040438470638322521735993 1530328852978741891301995)
      ·
        refine ⟨2295493279468112836952993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530328852978741891301995 2295493279468112836952993)
        ·
          refine ⟨1721619959601084627714745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295493279468112836952993 1721619959601084627714745)
          ·
            refine ⟨1291214969700813470786059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721619959601084627714745 1291214969700813470786059)
            ·
              refine ⟨1936822454551220206179089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291214969700813470786059 1936822454551220206179089)
              ·
                refine ⟨1452616840913415154634317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936822454551220206179089 1452616840913415154634317)
                ·
                  refine ⟨544731315342530682987869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1452616840913415154634317 544731315342530682987869)
                  ·
                    refine ⟨204274243253449006120451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544731315342530682987869 204274243253449006120451)
                    ·
                      rfl

theorem cell22_596734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_596734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596734 prefixEnd_596734 := by exact prefixLift 596734
  have htrace : WordTrace (prefixWord ++ tailWord_596734) baseStart_596734 baseEnd_596734 := by
    simpa [prefixWord, tailWord_596734, baseEnd_596734] using wordTrace_append hprefix tailTrace_596734
  have hstable : (prefixWord ++ tailWord_596734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596734).length < 2 ^ (prefixWord ++ tailWord_596734).sum := by decide
  have hdescent : baseEnd_596734 < baseStart_596734 := by decide
  rcases family_descends (prefixWord ++ tailWord_596734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596794 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_596794 : Nat := 118140960795 + 596794 * 2 ^ 59
def prefixEnd_596794 : Nat := 4983230072969 + 3 ^ 40 * 596794 * 2
def baseEnd_596794 : Nat := 204294782479628849620267

theorem tailTrace_596794 : CollatzResearch.WordTrace tailWord_596794 prefixEnd_596794 204294782479628849620267 := by
  unfold tailWord_596794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441716349981184286425359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14511243599949824763800957 5441716349981184286425359)
  ·
    refine ⟨8162574524971776429638039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441716349981184286425359 8162574524971776429638039)
    ·
      refine ⟨12243861787457664644457059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8162574524971776429638039 12243861787457664644457059)
      ·
        refine ⟨18365792681186496966685589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12243861787457664644457059 18365792681186496966685589)
        ·
          refine ⟨860896531930617045313387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18365792681186496966685589 860896531930617045313387)
          ·
            refine ⟨1291344797895925567970081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860896531930617045313387 1291344797895925567970081)
            ·
              refine ⟨968508598421944175977561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1291344797895925567970081 968508598421944175977561)
              ·
                refine ⟨726381448816458131983171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968508598421944175977561 726381448816458131983171)
                ·
                  refine ⟨1089572173224687197974757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726381448816458131983171 1089572173224687197974757)
                  ·
                    refine ⟨204294782479628849620267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1089572173224687197974757 204294782479628849620267)
                    ·
                      rfl

theorem cell22_596794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_596794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596794 prefixEnd_596794 := by exact prefixLift 596794
  have htrace : WordTrace (prefixWord ++ tailWord_596794) baseStart_596794 baseEnd_596794 := by
    simpa [prefixWord, tailWord_596794, baseEnd_596794] using wordTrace_append hprefix tailTrace_596794
  have hstable : (prefixWord ++ tailWord_596794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596794).length < 2 ^ (prefixWord ++ tailWord_596794).sum := by decide
  have hdescent : baseEnd_596794 < baseStart_596794 := by decide
  rcases family_descends (prefixWord ++ tailWord_596794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596809 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 4]
def baseStart_596809 : Nat := 118140960795 + 596809 * 2 ^ 59
def prefixEnd_596809 : Nat := 4983230072969 + 3 ^ 40 * 596809 * 2
def baseEnd_596809 : Nat := 68099972428724603498407

theorem tailTrace_596809 : CollatzResearch.WordTrace tailWord_596809 prefixEnd_596809 68099972428724603498407 := by
  unfold tailWord_596809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21767412494870394707497481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14511608329913596471664987 21767412494870394707497481)
  ·
    refine ⟨16325559371152796030623111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21767412494870394707497481 16325559371152796030623111)
    ·
      refine ⟨24488339056729194045934667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16325559371152796030623111 24488339056729194045934667)
      ·
        refine ⟨36732508585093791068902001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24488339056729194045934667 36732508585093791068902001)
        ·
          refine ⟨27549381438820343301676501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36732508585093791068902001 27549381438820343301676501)
          ·
            refine ⟨645688627472351796133043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27549381438820343301676501 645688627472351796133043)
            ·
              refine ⟨968532941208527694199565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645688627472351796133043 968532941208527694199565)
              ·
                refine ⟨363199852953197885324837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 968532941208527694199565 363199852953197885324837)
                ·
                  refine ⟨68099972428724603498407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363199852953197885324837 68099972428724603498407)
                  ·
                    rfl

theorem cell22_596809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_596809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596809 prefixEnd_596809 := by exact prefixLift 596809
  have htrace : WordTrace (prefixWord ++ tailWord_596809) baseStart_596809 baseEnd_596809 := by
    simpa [prefixWord, tailWord_596809, baseEnd_596809] using wordTrace_append hprefix tailTrace_596809
  have hstable : (prefixWord ++ tailWord_596809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596809).length < 2 ^ (prefixWord ++ tailWord_596809).sum := by decide
  have hdescent : baseEnd_596809 < baseStart_596809 := by decide
  rcases family_descends (prefixWord ++ tailWord_596809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596897 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_596897 : Nat := 118140960795 + 596897 * 2 ^ 59
def prefixEnd_596897 : Nat := 4983230072969 + 3 ^ 40 * 596897 * 2
def baseEnd_596897 : Nat := 204330041484570914294951

theorem tailTrace_596897 : CollatzResearch.WordTrace tailWord_596897 prefixEnd_596897 204330041484570914294951 := by
  unfold tailWord_596897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21770622118551585736700945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14513748079034390491133963 21770622118551585736700945)
  ·
    refine ⟨16327966588913689302525709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21770622118551585736700945 16327966588913689302525709)
    ·
      refine ⟨6122987470842633488447141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16327966588913689302525709 6122987470842633488447141)
      ·
        refine ⟨1148060150782993779083839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6122987470842633488447141 1148060150782993779083839)
        ·
          refine ⟨1722090226174490668625759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148060150782993779083839 1722090226174490668625759)
          ·
            refine ⟨2583135339261736002938639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722090226174490668625759 2583135339261736002938639)
            ·
              refine ⟨3874703008892604004407959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583135339261736002938639 3874703008892604004407959)
              ·
                refine ⟨5812054513338906006611939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874703008892604004407959 5812054513338906006611939)
                ·
                  refine ⟨8718081770008359009917909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5812054513338906006611939 8718081770008359009917909)
                  ·
                    refine ⟨204330041484570914294951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8718081770008359009917909 204330041484570914294951)
                    ·
                      rfl

theorem cell22_596897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_596897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_596897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_596897 prefixEnd_596897 := by exact prefixLift 596897
  have htrace : WordTrace (prefixWord ++ tailWord_596897) baseStart_596897 baseEnd_596897 := by
    simpa [prefixWord, tailWord_596897, baseEnd_596897] using wordTrace_append hprefix tailTrace_596897
  have hstable : (prefixWord ++ tailWord_596897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596897).length < 2 ^ (prefixWord ++ tailWord_596897).sum := by decide
  have hdescent : baseEnd_596897 < baseStart_596897 := by decide
  rcases family_descends (prefixWord ++ tailWord_596897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597038 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_597038 : Nat := 118140960795 + 597038 * 2 ^ 59
def prefixEnd_597038 : Nat := 4983230072969 + 3 ^ 40 * 597038 * 2
def baseEnd_597038 : Nat := 204378308666093546519519

theorem tailTrace_597038 : CollatzResearch.WordTrace tailWord_597038 prefixEnd_597038 204378308666093546519519 := by
  unfold tailWord_597038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721970601380095852197971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14517176540693844545055845 2721970601380095852197971)
  ·
    refine ⟨4082955902070143778296957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2721970601380095852197971 4082955902070143778296957)
    ·
      refine ⟨1531108463276303916861359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4082955902070143778296957 1531108463276303916861359)
      ·
        refine ⟨2296662694914455875292039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531108463276303916861359 2296662694914455875292039)
        ·
          refine ⟨3444994042371683812938059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296662694914455875292039 3444994042371683812938059)
          ·
            refine ⟨5167491063557525719407089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444994042371683812938059 5167491063557525719407089)
            ·
              refine ⟨3875618297668144289555317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167491063557525719407089 3875618297668144289555317)
              ·
                refine ⟨363339215406388527145811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3875618297668144289555317 363339215406388527145811)
                ·
                  refine ⟨545008823109582790718717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363339215406388527145811 545008823109582790718717)
                  ·
                    refine ⟨204378308666093546519519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545008823109582790718717 204378308666093546519519)
                    ·
                      rfl

theorem cell22_597038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_597038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597038 prefixEnd_597038 := by exact prefixLift 597038
  have htrace : WordTrace (prefixWord ++ tailWord_597038) baseStart_597038 baseEnd_597038 := by
    simpa [prefixWord, tailWord_597038, baseEnd_597038] using wordTrace_append hprefix tailTrace_597038
  have hstable : (prefixWord ++ tailWord_597038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597038).length < 2 ^ (prefixWord ++ tailWord_597038).sum := by decide
  have hdescent : baseEnd_597038 < baseStart_597038 := by decide
  rcases family_descends (prefixWord ++ tailWord_597038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597098 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_597098 : Nat := 118140960795 + 597098 * 2 ^ 59
def prefixEnd_597098 : Nat := 4983230072969 + 3 ^ 40 * 597098 * 2
def baseEnd_597098 : Nat := 204398847892273390019335

theorem tailTrace_597098 : CollatzResearch.WordTrace tailWord_597098 prefixEnd_597098 204398847892273390019335 := by
  unfold tailWord_597098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5444488297705849266191987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14518635460548931376511965 5444488297705849266191987)
  ·
    refine ⟨8166732446558773899287981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5444488297705849266191987 8166732446558773899287981)
    ·
      refine ⟨3062524667459540212232993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8166732446558773899287981 3062524667459540212232993)
      ·
        refine ⟨2296893500594655159174745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3062524667459540212232993 2296893500594655159174745)
        ·
          refine ⟨1722670125445991369381059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296893500594655159174745 1722670125445991369381059)
          ·
            refine ⟨2584005188168987054071589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722670125445991369381059 2584005188168987054071589)
            ·
              refine ⟨484500972781685072638423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2584005188168987054071589 484500972781685072638423)
              ·
                refine ⟨726751459172527608957635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484500972781685072638423 726751459172527608957635)
                ·
                  refine ⟨1090127188758791413436453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726751459172527608957635 1090127188758791413436453)
                  ·
                    refine ⟨204398847892273390019335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1090127188758791413436453 204398847892273390019335)
                    ·
                      rfl

theorem cell22_597098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_597098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597098 prefixEnd_597098 := by exact prefixLift 597098
  have htrace : WordTrace (prefixWord ++ tailWord_597098) baseStart_597098 baseEnd_597098 := by
    simpa [prefixWord, tailWord_597098, baseEnd_597098] using wordTrace_append hprefix tailTrace_597098
  have hstable : (prefixWord ++ tailWord_597098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597098).length < 2 ^ (prefixWord ++ tailWord_597098).sum := by decide
  have hdescent : baseEnd_597098 < baseStart_597098 := by decide
  rcases family_descends (prefixWord ++ tailWord_597098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597128 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_597128 : Nat := 118140960795 + 597128 * 2 ^ 59
def prefixEnd_597128 : Nat := 4983230072969 + 3 ^ 40 * 597128 * 2
def baseEnd_597128 : Nat := 204409117505363311769243

theorem tailTrace_597128 : CollatzResearch.WordTrace tailWord_597128 prefixEnd_597128 204409117505363311769243 := by
  unfold tailWord_597128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10889523690357356094180019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14519364920476474792240025 10889523690357356094180019)
  ·
    refine ⟨16334285535536034141270029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10889523690357356094180019 16334285535536034141270029)
    ·
      refine ⟨6125357075826012802976261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16334285535536034141270029 6125357075826012802976261)
      ·
        refine ⟨1148504451717377400558049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6125357075826012802976261 1148504451717377400558049)
        ·
          refine ⟨861378338788033050418537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1148504451717377400558049 861378338788033050418537)
          ·
            refine ⟨646033754091024787813903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861378338788033050418537 646033754091024787813903)
            ·
              refine ⟨969050631136537181720855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646033754091024787813903 969050631136537181720855)
              ·
                refine ⟨1453575946704805772581283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969050631136537181720855 1453575946704805772581283)
                ·
                  refine ⟨2180363920057208658871925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453575946704805772581283 2180363920057208658871925)
                  ·
                    refine ⟨204409117505363311769243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2180363920057208658871925 204409117505363311769243)
                    ·
                      rfl

theorem cell22_597128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_597128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597128 prefixEnd_597128 := by exact prefixLift 597128
  have htrace : WordTrace (prefixWord ++ tailWord_597128) baseStart_597128 baseEnd_597128 := by
    simpa [prefixWord, tailWord_597128, baseEnd_597128] using wordTrace_append hprefix tailTrace_597128
  have hstable : (prefixWord ++ tailWord_597128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597128).length < 2 ^ (prefixWord ++ tailWord_597128).sum := by decide
  have hdescent : baseEnd_597128 < baseStart_597128 := by decide
  rcases family_descends (prefixWord ++ tailWord_597128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597289 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_597289 : Nat := 118140960795 + 597289 * 2 ^ 59
def prefixEnd_597289 : Nat := 4983230072969 + 3 ^ 40 * 597289 * 2
def baseEnd_597289 : Nat := 204464231095612558493749

theorem tailTrace_597289 : CollatzResearch.WordTrace tailWord_597289 prefixEnd_597289 204464231095612558493749 := by
  unfold tailWord_597289
  simp only [CollatzResearch.WordTrace]
  refine ⟨21784919533131436684970921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14523279688754291123313947 21784919533131436684970921)
  ·
    refine ⟨16338689649848577513728191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21784919533131436684970921 16338689649848577513728191)
    ·
      refine ⟨24508034474772866270592287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16338689649848577513728191 24508034474772866270592287)
      ·
        refine ⟨36762051712159299405888431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24508034474772866270592287 36762051712159299405888431)
        ·
          refine ⟨55143077568238949108832647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36762051712159299405888431 55143077568238949108832647)
          ·
            refine ⟨82714616352358423663248971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55143077568238949108832647 82714616352358423663248971)
            ·
              refine ⟨124071924528537635494873457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82714616352358423663248971 124071924528537635494873457)
              ·
                refine ⟨93053943396403226621155093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124071924528537635494873457 93053943396403226621155093)
                ·
                  refine ⟨4361903596706401247866645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93053943396403226621155093 4361903596706401247866645)
                  ·
                    refine ⟨204464231095612558493749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4361903596706401247866645 204464231095612558493749)
                    ·
                      rfl

theorem cell22_597289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_597289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597289 prefixEnd_597289 := by exact prefixLift 597289
  have htrace : WordTrace (prefixWord ++ tailWord_597289) baseStart_597289 baseEnd_597289 := by
    simpa [prefixWord, tailWord_597289, baseEnd_597289] using wordTrace_append hprefix tailTrace_597289
  have hstable : (prefixWord ++ tailWord_597289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597289).length < 2 ^ (prefixWord ++ tailWord_597289).sum := by decide
  have hdescent : baseEnd_597289 < baseStart_597289 := by decide
  rcases family_descends (prefixWord ++ tailWord_597289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597308 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_597308 : Nat := 118140960795 + 597308 * 2 ^ 59
def prefixEnd_597308 : Nat := 4983230072969 + 3 ^ 40 * 597308 * 2
def baseEnd_597308 : Nat := 204470735183902842268691

theorem tailTrace_597308 : CollatzResearch.WordTrace tailWord_597308 prefixEnd_597308 204470735183902842268691 := by
  unfold tailWord_597308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10892806260031301464956289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14523741680041735286608385 10892806260031301464956289)
  ·
    refine ⟨8169604695023476098717217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10892806260031301464956289 8169604695023476098717217)
    ·
      refine ⟨6127203521267607074037913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8169604695023476098717217 6127203521267607074037913)
      ·
        refine ⟨4595402640950705305528435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6127203521267607074037913 4595402640950705305528435)
        ·
          refine ⟨6893103961426057958292653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595402640950705305528435 6893103961426057958292653)
          ·
            refine ⟨2584913985534771734359745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6893103961426057958292653 2584913985534771734359745)
            ·
              refine ⟨1938685489151078800769809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584913985534771734359745 1938685489151078800769809)
              ·
                refine ⟨1454014116863309100577357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1938685489151078800769809 1454014116863309100577357)
                ·
                  refine ⟨545255293823740912716509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1454014116863309100577357 545255293823740912716509)
                  ·
                    refine ⟨204470735183902842268691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545255293823740912716509 204470735183902842268691)
                    ·
                      rfl

theorem cell22_597308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_597308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597308 prefixEnd_597308 := by exact prefixLift 597308
  have htrace : WordTrace (prefixWord ++ tailWord_597308) baseStart_597308 baseEnd_597308 := by
    simpa [prefixWord, tailWord_597308, baseEnd_597308] using wordTrace_append hprefix tailTrace_597308
  have hstable : (prefixWord ++ tailWord_597308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597308).length < 2 ^ (prefixWord ++ tailWord_597308).sum := by decide
  have hdescent : baseEnd_597308 < baseStart_597308 := by decide
  rcases family_descends (prefixWord ++ tailWord_597308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597381 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_597381 : Nat := 118140960795 + 597381 * 2 ^ 59
def prefixEnd_597381 : Nat := 4983230072969 + 3 ^ 40 * 597381 * 2
def baseEnd_597381 : Nat := 204495724575754985193467

theorem tailTrace_597381 : CollatzResearch.WordTrace tailWord_597381 prefixEnd_597381 204495724575754985193467 := by
  unfold tailWord_597381
  simp only [CollatzResearch.WordTrace]
  refine ⟨21788275048798136397319997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14525516699198757598213331 21788275048798136397319997)
  ·
    refine ⟨8170603143299301148994999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21788275048798136397319997 8170603143299301148994999)
    ·
      refine ⟨12255904714948951723492499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8170603143299301148994999 12255904714948951723492499)
      ·
        refine ⟨18383857072423427585238749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12255904714948951723492499 18383857072423427585238749)
        ·
          refine ⟨6893946402158785344464531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18383857072423427585238749 6893946402158785344464531)
          ·
            refine ⟨10340919603238178016696797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893946402158785344464531 10340919603238178016696797)
            ·
              refine ⟨3877844851214316756261299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10340919603238178016696797 3877844851214316756261299)
              ·
                refine ⟨5816767276821475134391949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877844851214316756261299 5816767276821475134391949)
                ·
                  refine ⟨2181287728808053175396981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5816767276821475134391949 2181287728808053175396981)
                  ·
                    refine ⟨204495724575754985193467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2181287728808053175396981 204495724575754985193467)
                    ·
                      rfl

theorem cell22_597381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_597381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597381 prefixEnd_597381 := by exact prefixLift 597381
  have htrace : WordTrace (prefixWord ++ tailWord_597381) baseStart_597381 baseEnd_597381 := by
    simpa [prefixWord, tailWord_597381, baseEnd_597381] using wordTrace_append hprefix tailTrace_597381
  have hstable : (prefixWord ++ tailWord_597381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597381).length < 2 ^ (prefixWord ++ tailWord_597381).sum := by decide
  have hdescent : baseEnd_597381 < baseStart_597381 := by decide
  rcases family_descends (prefixWord ++ tailWord_597381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597415 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 2, 3]
def baseStart_597415 : Nat := 118140960795 + 597415 * 2 ^ 59
def prefixEnd_597415 : Nat := 4983230072969 + 3 ^ 40 * 597415 * 2
def baseEnd_597415 : Nat := 204507363470590229843363

theorem tailTrace_597415 : CollatzResearch.WordTrace tailWord_597415 prefixEnd_597415 204507363470590229843363 := by
  unfold tailWord_597415
  simp only [CollatzResearch.WordTrace]
  refine ⟨21789515130674960204057699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14526343420449973469371799 21789515130674960204057699)
  ·
    refine ⟨32684272696012440306086549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21789515130674960204057699 32684272696012440306086549)
    ·
      refine ⟨1532075282625583139347807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32684272696012440306086549 1532075282625583139347807)
      ·
        refine ⟨2298112923938374709021711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532075282625583139347807 2298112923938374709021711)
        ·
          refine ⟨3447169385907562063532567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298112923938374709021711 3447169385907562063532567)
          ·
            refine ⟨5170754078861343095298851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447169385907562063532567 5170754078861343095298851)
            ·
              refine ⟨7756131118292014642948277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5170754078861343095298851 7756131118292014642948277)
              ·
                refine ⟨727137292339876372776401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7756131118292014642948277 727137292339876372776401)
                ·
                  refine ⟨545352969254907279582301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727137292339876372776401 545352969254907279582301)
                  ·
                    refine ⟨204507363470590229843363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545352969254907279582301 204507363470590229843363)
                    ·
                      rfl

theorem cell22_597415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_597415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597415 prefixEnd_597415 := by exact prefixLift 597415
  have htrace : WordTrace (prefixWord ++ tailWord_597415) baseStart_597415 baseEnd_597415 := by
    simpa [prefixWord, tailWord_597415, baseEnd_597415] using wordTrace_append hprefix tailTrace_597415
  have hstable : (prefixWord ++ tailWord_597415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597415).length < 2 ^ (prefixWord ++ tailWord_597415).sum := by decide
  have hdescent : baseEnd_597415 < baseStart_597415 := by decide
  rcases family_descends (prefixWord ++ tailWord_597415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597426 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_597426 : Nat := 118140960795 + 597426 * 2 ^ 59
def prefixEnd_597426 : Nat := 4983230072969 + 3 ^ 40 * 597426 * 2
def baseEnd_597426 : Nat := 204511128995389867818329

theorem tailTrace_597426 : CollatzResearch.WordTrace tailWord_597426 prefixEnd_597426 204511128995389867818329 := by
  unfold tailWord_597426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5447479083408777270677033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14526610889090072721805421 5447479083408777270677033)
  ·
    refine ⟨4085609312556582953007775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5447479083408777270677033 4085609312556582953007775)
    ·
      refine ⟨6128413968834874429511663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4085609312556582953007775 6128413968834874429511663)
      ·
        refine ⟨9192620953252311644267495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6128413968834874429511663 9192620953252311644267495)
        ·
          refine ⟨13788931429878467466401243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9192620953252311644267495 13788931429878467466401243)
          ·
            refine ⟨20683397144817701199601865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13788931429878467466401243 20683397144817701199601865)
            ·
              refine ⟨15512547858613275899701399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20683397144817701199601865 15512547858613275899701399)
              ·
                refine ⟨23268821787919913849552099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15512547858613275899701399 23268821787919913849552099)
                ·
                  refine ⟨34903232681879870774328149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23268821787919913849552099 34903232681879870774328149)
                  ·
                    refine ⟨204511128995389867818329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34903232681879870774328149 204511128995389867818329)
                    ·
                      rfl

theorem cell22_597426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_597426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597426 prefixEnd_597426 := by exact prefixLift 597426
  have htrace : WordTrace (prefixWord ++ tailWord_597426) baseStart_597426 baseEnd_597426 := by
    simpa [prefixWord, tailWord_597426, baseEnd_597426] using wordTrace_append hprefix tailTrace_597426
  have hstable : (prefixWord ++ tailWord_597426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597426).length < 2 ^ (prefixWord ++ tailWord_597426).sum := by decide
  have hdescent : baseEnd_597426 < baseStart_597426 := by decide
  rcases family_descends (prefixWord ++ tailWord_597426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597456 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_597456 : Nat := 118140960795 + 597456 * 2 ^ 59
def prefixEnd_597456 : Nat := 4983230072969 + 3 ^ 40 * 597456 * 2
def baseEnd_597456 : Nat := 68173799536159929856079

theorem tailTrace_597456 : CollatzResearch.WordTrace tailWord_597456 prefixEnd_597456 68173799536159929856079 := by
  unfold tailWord_597456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895505261763212103150111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14527340349017616137533481 10895505261763212103150111)
  ·
    refine ⟨16343257892644818154725167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10895505261763212103150111 16343257892644818154725167)
    ·
      refine ⟨24514886838967227232087751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16343257892644818154725167 24514886838967227232087751)
      ·
        refine ⟨36772330258450840848131627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24514886838967227232087751 36772330258450840848131627)
        ·
          refine ⟨55158495387676261272197441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36772330258450840848131627 55158495387676261272197441)
          ·
            refine ⟨41368871540757195954148081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55158495387676261272197441 41368871540757195954148081)
            ·
              refine ⟨31026653655567896965611061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41368871540757195954148081 31026653655567896965611061)
              ·
                refine ⟨2908748780209490340526037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31026653655567896965611061 2908748780209490340526037)
                ·
                  refine ⟨68173799536159929856079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2908748780209490340526037 68173799536159929856079)
                  ·
                    rfl

theorem cell22_597456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_597456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597456 prefixEnd_597456 := by exact prefixLift 597456
  have htrace : WordTrace (prefixWord ++ tailWord_597456) baseStart_597456 baseEnd_597456 := by
    simpa [prefixWord, tailWord_597456, baseEnd_597456] using wordTrace_append hprefix tailTrace_597456
  have hstable : (prefixWord ++ tailWord_597456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597456).length < 2 ^ (prefixWord ++ tailWord_597456).sum := by decide
  have hdescent : baseEnd_597456 < baseStart_597456 := by decide
  rcases family_descends (prefixWord ++ tailWord_597456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597494 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_597494 : Nat := 118140960795 + 597494 * 2 ^ 59
def prefixEnd_597494 : Nat := 4983230072969 + 3 ^ 40 * 597494 * 2
def baseEnd_597494 : Nat := 204534406785060357118121

theorem tailTrace_597494 : CollatzResearch.WordTrace tailWord_597494 prefixEnd_597494 204534406785060357118121 := by
  unfold tailWord_597494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362024781086797293511471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14528264331592504464122357 1362024781086797293511471)
  ·
    refine ⟨2043037171630195940267207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1362024781086797293511471 2043037171630195940267207)
    ·
      refine ⟨3064555757445293910400811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043037171630195940267207 3064555757445293910400811)
      ·
        refine ⟨4596833636167940865601217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3064555757445293910400811 4596833636167940865601217)
        ·
          refine ⟨3447625227125955649200913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4596833636167940865601217 3447625227125955649200913)
          ·
            refine ⟨2585718920344466736900685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3447625227125955649200913 2585718920344466736900685)
            ·
              refine ⟨969644595129175026337757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2585718920344466736900685 969644595129175026337757)
              ·
                refine ⟨363616723173440634876659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 969644595129175026337757 363616723173440634876659)
                ·
                  refine ⟨545425084760160952314989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363616723173440634876659 545425084760160952314989)
                  ·
                    refine ⟨204534406785060357118121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545425084760160952314989 204534406785060357118121)
                    ·
                      rfl

theorem cell22_597494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_597494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597494 prefixEnd_597494 := by exact prefixLift 597494
  have htrace : WordTrace (prefixWord ++ tailWord_597494) baseStart_597494 baseEnd_597494 := by
    simpa [prefixWord, tailWord_597494, baseEnd_597494] using wordTrace_append hprefix tailTrace_597494
  have hstable : (prefixWord ++ tailWord_597494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597494).length < 2 ^ (prefixWord ++ tailWord_597494).sum := by decide
  have hdescent : baseEnd_597494 < baseStart_597494 := by decide
  rcases family_descends (prefixWord ++ tailWord_597494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597537 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_597537 : Nat := 118140960795 + 597537 * 2 ^ 59
def prefixEnd_597537 : Nat := 4983230072969 + 3 ^ 40 * 597537 * 2
def baseEnd_597537 : Nat := 204549126563822578292989

theorem tailTrace_597537 : CollatzResearch.WordTrace tailWord_597537 prefixEnd_597537 204549126563822578292989 := by
  unfold tailWord_597537
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793964836232975039998865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14529309890821983359999243 21793964836232975039998865)
  ·
    refine ⟨16345473627174731279999149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21793964836232975039998865 16345473627174731279999149)
    ·
      refine ⟨6129552610190524229999681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16345473627174731279999149 6129552610190524229999681)
      ·
        refine ⟨4597164457642893172499761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6129552610190524229999681 4597164457642893172499761)
        ·
          refine ⟨3447873343232169879374821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4597164457642893172499761 3447873343232169879374821)
          ·
            refine ⟨646476251856031852382779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3447873343232169879374821 646476251856031852382779)
            ·
              refine ⟨969714377784047778574169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646476251856031852382779 969714377784047778574169)
              ·
                refine ⟨727285783338035833930627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969714377784047778574169 727285783338035833930627)
                ·
                  refine ⟨1090928675007053750895941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727285783338035833930627 1090928675007053750895941)
                  ·
                    refine ⟨204549126563822578292989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1090928675007053750895941 204549126563822578292989)
                    ·
                      rfl

theorem cell22_597537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_597537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597537 prefixEnd_597537 := by exact prefixLift 597537
  have htrace : WordTrace (prefixWord ++ tailWord_597537) baseStart_597537 baseEnd_597537 := by
    simpa [prefixWord, tailWord_597537, baseEnd_597537] using wordTrace_append hprefix tailTrace_597537
  have hstable : (prefixWord ++ tailWord_597537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597537).length < 2 ^ (prefixWord ++ tailWord_597537).sum := by decide
  have hdescent : baseEnd_597537 < baseStart_597537 := by decide
  rcases family_descends (prefixWord ++ tailWord_597537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597550 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_597550 : Nat := 118140960795 + 597550 * 2 ^ 59
def prefixEnd_597550 : Nat := 4983230072969 + 3 ^ 40 * 597550 * 2
def baseEnd_597550 : Nat := 204553576729494877717949

theorem tailTrace_597550 : CollatzResearch.WordTrace tailWord_597550 prefixEnd_597550 204553576729494877717949 := by
  unfold tailWord_597550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724304873148234782527763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14529625990123918840148069 2724304873148234782527763)
  ·
    refine ⟨4086457309722352173791645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2724304873148234782527763 4086457309722352173791645)
    ·
      refine ⟨1532421491145882065171867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4086457309722352173791645 1532421491145882065171867)
      ·
        refine ⟨2298632236718823097757801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532421491145882065171867 2298632236718823097757801)
        ·
          refine ⟨1723974177539117323318351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298632236718823097757801 1723974177539117323318351)
          ·
            refine ⟨2585961266308675984977527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723974177539117323318351 2585961266308675984977527)
            ·
              refine ⟨3878941899463013977466291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585961266308675984977527 3878941899463013977466291)
              ·
                refine ⟨5818412849194520966199437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878941899463013977466291 5818412849194520966199437)
                ·
                  refine ⟨2181904818447945362324789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5818412849194520966199437 2181904818447945362324789)
                  ·
                    refine ⟨204553576729494877717949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2181904818447945362324789 204553576729494877717949)
                    ·
                      rfl

theorem cell22_597550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_597550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597550 prefixEnd_597550 := by exact prefixLift 597550
  have htrace : WordTrace (prefixWord ++ tailWord_597550) baseStart_597550 baseEnd_597550 := by
    simpa [prefixWord, tailWord_597550, baseEnd_597550] using wordTrace_append hprefix tailTrace_597550
  have hstable : (prefixWord ++ tailWord_597550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597550).length < 2 ^ (prefixWord ++ tailWord_597550).sum := by decide
  have hdescent : baseEnd_597550 < baseStart_597550 := by decide
  rcases family_descends (prefixWord ++ tailWord_597550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597567 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 2, 3]
def baseStart_597567 : Nat := 118140960795 + 597567 * 2 ^ 59
def prefixEnd_597567 : Nat := 4983230072969 + 3 ^ 40 * 597567 * 2
def baseEnd_597567 : Nat := 204559396176912500042897

theorem tailTrace_597567 : CollatzResearch.WordTrace tailWord_597567 prefixEnd_597567 204559396176912500042897 := by
  unfold tailWord_597567
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795059026124290163590955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14530039350749526775727303 21795059026124290163590955)
  ·
    refine ⟨32692588539186435245386433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21795059026124290163590955 32692588539186435245386433)
    ·
      refine ⟨24519441404389826434039825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32692588539186435245386433 24519441404389826434039825)
      ·
        refine ⟨18389581053292369825529869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24519441404389826434039825 18389581053292369825529869)
        ·
          refine ⟨6896092894984638684573701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18389581053292369825529869 6896092894984638684573701)
          ·
            refine ⟨1293017417809619753357569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6896092894984638684573701 1293017417809619753357569)
            ·
              refine ⟨969763063357214815018177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293017417809619753357569 969763063357214815018177)
              ·
                refine ⟨727322297517911111263633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969763063357214815018177 727322297517911111263633)
                ·
                  refine ⟨545491723138433333447725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727322297517911111263633 545491723138433333447725)
                  ·
                    refine ⟨204559396176912500042897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545491723138433333447725 204559396176912500042897)
                    ·
                      rfl

theorem cell22_597567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_597567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597567 prefixEnd_597567 := by exact prefixLift 597567
  have htrace : WordTrace (prefixWord ++ tailWord_597567) baseStart_597567 baseEnd_597567 := by
    simpa [prefixWord, tailWord_597567, baseEnd_597567] using wordTrace_append hprefix tailTrace_597567
  have hstable : (prefixWord ++ tailWord_597567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597567).length < 2 ^ (prefixWord ++ tailWord_597567).sum := by decide
  have hdescent : baseEnd_597567 < baseStart_597567 := by decide
  rcases family_descends (prefixWord ++ tailWord_597567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597580 : List Nat := [2, 2, 1, 3, 1, 5, 1, 7]
def baseStart_597580 : Nat := 118140960795 + 597580 * 2 ^ 59
def prefixEnd_597580 : Nat := 4983230072969 + 3 ^ 40 * 597580 * 2
def baseEnd_597580 : Nat := 22729316260287199940873

theorem tailTrace_597580 : CollatzResearch.WordTrace tailWord_597580 prefixEnd_597580 22729316260287199940873 := by
  unfold tailWord_597580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10897766587538596691907097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14530355450051462255876129 10897766587538596691907097)
  ·
    refine ⟨8173324940653947518930323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10897766587538596691907097 8173324940653947518930323)
    ·
      refine ⟨12259987410980921278395485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8173324940653947518930323 12259987410980921278395485)
      ·
        refine ⟨4597495279117845479398307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12259987410980921278395485 4597495279117845479398307)
        ·
          refine ⟨6896242918676768219097461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597495279117845479398307 6896242918676768219097461)
          ·
            refine ⟨646522773625947020540387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6896242918676768219097461 646522773625947020540387)
            ·
              refine ⟨969784160438920530810581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646522773625947020540387 969784160438920530810581)
              ·
                refine ⟨22729316260287199940873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 969784160438920530810581 22729316260287199940873)
                ·
                  rfl

theorem cell22_597580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 7].length) (baseStart_597580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597580 prefixEnd_597580 := by exact prefixLift 597580
  have htrace : WordTrace (prefixWord ++ tailWord_597580) baseStart_597580 baseEnd_597580 := by
    simpa [prefixWord, tailWord_597580, baseEnd_597580] using wordTrace_append hprefix tailTrace_597580
  have hstable : (prefixWord ++ tailWord_597580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597580).length < 2 ^ (prefixWord ++ tailWord_597580).sum := by decide
  have hdescent : baseEnd_597580 < baseStart_597580 := by decide
  rcases family_descends (prefixWord ++ tailWord_597580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597629 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_597629 : Nat := 118140960795 + 597629 * 2 ^ 59
def prefixEnd_597629 : Nat := 4983230072969 + 3 ^ 40 * 597629 * 2
def baseEnd_597629 : Nat := 204580620043965004992707

theorem tailTrace_597629 : CollatzResearch.WordTrace tailWord_597629 prefixEnd_597629 204580620043965004992707 := by
  unfold tailWord_597629
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797320351899674752347941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14531546901266449834898627 21797320351899674752347941)
  ·
    refine ⟨4086997565981189016065239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21797320351899674752347941 4086997565981189016065239)
    ·
      refine ⟨6130496348971783524097859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086997565981189016065239 6130496348971783524097859)
      ·
        refine ⟨9195744523457675286146789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130496348971783524097859 9195744523457675286146789)
        ·
          refine ⟨1724202098148314116152523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9195744523457675286146789 1724202098148314116152523)
          ·
            refine ⟨2586303147222471174228785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724202098148314116152523 2586303147222471174228785)
            ·
              refine ⟨1939727360416853380671589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586303147222471174228785 1939727360416853380671589)
              ·
                refine ⟨363698880078160008875923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1939727360416853380671589 363698880078160008875923)
                ·
                  refine ⟨545548320117240013313885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363698880078160008875923 545548320117240013313885)
                  ·
                    refine ⟨204580620043965004992707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545548320117240013313885 204580620043965004992707)
                    ·
                      rfl

theorem cell22_597629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_597629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597629 prefixEnd_597629 := by exact prefixLift 597629
  have htrace : WordTrace (prefixWord ++ tailWord_597629) baseStart_597629 baseEnd_597629 := by
    simpa [prefixWord, tailWord_597629, baseEnd_597629] using wordTrace_append hprefix tailTrace_597629
  have hstable : (prefixWord ++ tailWord_597629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597629).length < 2 ^ (prefixWord ++ tailWord_597629).sum := by decide
  have hdescent : baseEnd_597629 < baseStart_597629 := by decide
  rcases family_descends (prefixWord ++ tailWord_597629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597663 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 1, 3]
def baseStart_597663 : Nat := 118140960795 + 597663 * 2 ^ 59
def prefixEnd_597663 : Nat := 4983230072969 + 3 ^ 40 * 597663 * 2
def baseEnd_597663 : Nat := 204592258938800249642603

theorem tailTrace_597663 : CollatzResearch.WordTrace tailWord_597663 prefixEnd_597663 204592258938800249642603 := by
  unfold tailWord_597663
  simp only [CollatzResearch.WordTrace]
  refine ⟨21798560433776498559085643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14532373622517665706057095 21798560433776498559085643)
  ·
    refine ⟨32697840650664747838628465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21798560433776498559085643 32697840650664747838628465)
    ·
      refine ⟨24523380487998560878971349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32697840650664747838628465 24523380487998560878971349)
      ·
        refine ⟨574766730187466270600891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24523380487998560878971349 574766730187466270600891)
        ·
          refine ⟨862150095281199405901337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574766730187466270600891 862150095281199405901337)
          ·
            refine ⟨646612571460899554426003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862150095281199405901337 646612571460899554426003)
            ·
              refine ⟨969918857191349331639005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646612571460899554426003 969918857191349331639005)
              ·
                refine ⟨363719571446755999364627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 969918857191349331639005 363719571446755999364627)
                ·
                  refine ⟨545579357170133999046941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363719571446755999364627 545579357170133999046941)
                  ·
                    refine ⟨204592258938800249642603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545579357170133999046941 204592258938800249642603)
                    ·
                      rfl

theorem cell22_597663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_597663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597663 prefixEnd_597663 := by exact prefixLift 597663
  have htrace : WordTrace (prefixWord ++ tailWord_597663) baseStart_597663 baseEnd_597663 := by
    simpa [prefixWord, tailWord_597663, baseEnd_597663] using wordTrace_append hprefix tailTrace_597663
  have hstable : (prefixWord ++ tailWord_597663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597663).length < 2 ^ (prefixWord ++ tailWord_597663).sum := by decide
  have hdescent : baseEnd_597663 < baseStart_597663 := by decide
  rcases family_descends (prefixWord ++ tailWord_597663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597687 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 6]
def baseStart_597687 : Nat := 118140960795 + 597687 * 2 ^ 59
def prefixEnd_597687 : Nat := 4983230072969 + 3 ^ 40 * 597687 * 2
def baseEnd_597687 : Nat := 68200158209757395680843

theorem tailTrace_597687 : CollatzResearch.WordTrace tailWord_597687 prefixEnd_597687 68200158209757395680843 := by
  unfold tailWord_597687
  simp only [CollatzResearch.WordTrace]
  refine ⟨21799435785689550657959315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14532957190459700438639543 21799435785689550657959315)
  ·
    refine ⟨32699153678534325986938973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21799435785689550657959315 32699153678534325986938973)
    ·
      refine ⟨12262182629450372245102115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32699153678534325986938973 12262182629450372245102115)
      ·
        refine ⟨18393273944175558367653173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12262182629450372245102115 18393273944175558367653173)
        ·
          refine ⟨1724369432266458596967485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18393273944175558367653173 1724369432266458596967485)
          ·
            refine ⟨646638537099921973862807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1724369432266458596967485 646638537099921973862807)
            ·
              refine ⟨969957805649882960794211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646638537099921973862807 969957805649882960794211)
              ·
                refine ⟨1454936708474824441191317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969957805649882960794211 1454936708474824441191317)
                ·
                  refine ⟨68200158209757395680843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1454936708474824441191317 68200158209757395680843)
                  ·
                    rfl

theorem cell22_597687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 6].length) (baseStart_597687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597687 prefixEnd_597687 := by exact prefixLift 597687
  have htrace : WordTrace (prefixWord ++ tailWord_597687) baseStart_597687 baseEnd_597687 := by
    simpa [prefixWord, tailWord_597687, baseEnd_597687] using wordTrace_append hprefix tailTrace_597687
  have hstable : (prefixWord ++ tailWord_597687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597687).length < 2 ^ (prefixWord ++ tailWord_597687).sum := by decide
  have hdescent : baseEnd_597687 < baseStart_597687 := by decide
  rcases family_descends (prefixWord ++ tailWord_597687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597706 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_597706 : Nat := 118140960795 + 597706 * 2 ^ 59
def prefixEnd_597706 : Nat := 4983230072969 + 3 ^ 40 * 597706 * 2
def baseEnd_597706 : Nat := 204606978717562470817471

theorem tailTrace_597706 : CollatzResearch.WordTrace tailWord_597706 prefixEnd_597706 204606978717562470817471 := by
  unfold tailWord_597706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450032193155179225725243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14533419181747144601933981 5450032193155179225725243)
  ·
    refine ⟨8175048289732768838587865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5450032193155179225725243 8175048289732768838587865)
    ·
      refine ⟨6131286217299576628940899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8175048289732768838587865 6131286217299576628940899)
      ·
        refine ⟨9196929325949364943411349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6131286217299576628940899 9196929325949364943411349)
        ·
          refine ⟨431106062153876481722407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9196929325949364943411349 431106062153876481722407)
          ·
            refine ⟨646659093230814722583611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431106062153876481722407 646659093230814722583611)
            ·
              refine ⟨969988639846222083875417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646659093230814722583611 969988639846222083875417)
              ·
                refine ⟨727491479884666562906563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969988639846222083875417 727491479884666562906563)
                ·
                  refine ⟨1091237219826999844359845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727491479884666562906563 1091237219826999844359845)
                  ·
                    refine ⟨204606978717562470817471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1091237219826999844359845 204606978717562470817471)
                    ·
                      rfl

theorem cell22_597706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_597706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597706 prefixEnd_597706 := by exact prefixLift 597706
  have htrace : WordTrace (prefixWord ++ tailWord_597706) baseStart_597706 baseEnd_597706 := by
    simpa [prefixWord, tailWord_597706, baseEnd_597706] using wordTrace_append hprefix tailTrace_597706
  have hstable : (prefixWord ++ tailWord_597706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597706).length < 2 ^ (prefixWord ++ tailWord_597706).sum := by decide
  have hdescent : baseEnd_597706 < baseStart_597706 := by decide
  rcases family_descends (prefixWord ++ tailWord_597706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597745 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_597745 : Nat := 118140960795 + 597745 * 2 ^ 59
def prefixEnd_597745 : Nat := 4983230072969 + 3 ^ 40 * 597745 * 2
def baseEnd_597745 : Nat := 204620329214579369092351

theorem tailTrace_597745 : CollatzResearch.WordTrace tailWord_597745 prefixEnd_597745 204620329214579369092351 := by
  unfold tailWord_597745
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801551219479426563570689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14534367479652951042380459 21801551219479426563570689)
  ·
    refine ⟨16351163414609569922678017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21801551219479426563570689 16351163414609569922678017)
    ·
      refine ⟨12263372560957177442008513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16351163414609569922678017 12263372560957177442008513)
      ·
        refine ⟨9197529420717883081506385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12263372560957177442008513 9197529420717883081506385)
        ·
          refine ⟨6898147065538412311129789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9197529420717883081506385 6898147065538412311129789)
          ·
            refine ⟨2586805149576904616673671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6898147065538412311129789 2586805149576904616673671)
            ·
              refine ⟨3880207724365356925010507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586805149576904616673671 3880207724365356925010507)
              ·
                refine ⟨5820311586548035387515761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880207724365356925010507 5820311586548035387515761)
                ·
                  refine ⟨4365233689911026540636821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5820311586548035387515761 4365233689911026540636821)
                  ·
                    refine ⟨204620329214579369092351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4365233689911026540636821 204620329214579369092351)
                    ·
                      rfl

theorem cell22_597745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_597745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597745 prefixEnd_597745 := by exact prefixLift 597745
  have htrace : WordTrace (prefixWord ++ tailWord_597745) baseStart_597745 baseEnd_597745 := by
    simpa [prefixWord, tailWord_597745, baseEnd_597745] using wordTrace_append hprefix tailTrace_597745
  have hstable : (prefixWord ++ tailWord_597745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597745).length < 2 ^ (prefixWord ++ tailWord_597745).sum := by decide
  have hdescent : baseEnd_597745 < baseStart_597745 := by decide
  rcases family_descends (prefixWord ++ tailWord_597745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597762 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_597762 : Nat := 118140960795 + 597762 * 2 ^ 59
def prefixEnd_597762 : Nat := 4983230072969 + 3 ^ 40 * 597762 * 2
def baseEnd_597762 : Nat := 204626148661996991417299

theorem tailTrace_597762 : CollatzResearch.WordTrace tailWord_597762 prefixEnd_597762 204626148661996991417299 := by
  unfold tailWord_597762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450542815104459616734885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14534780840278558977959693 5450542815104459616734885)
  ·
    refine ⟨1021976777832086178137791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5450542815104459616734885 1021976777832086178137791)
    ·
      refine ⟨1532965166748129267206687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021976777832086178137791 1532965166748129267206687)
      ·
        refine ⟨2299447750122193900810031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532965166748129267206687 2299447750122193900810031)
        ·
          refine ⟨3449171625183290851215047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299447750122193900810031 3449171625183290851215047)
          ·
            refine ⟨5173757437774936276822571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449171625183290851215047 5173757437774936276822571)
            ·
              refine ⟨7760636156662404415233857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173757437774936276822571 7760636156662404415233857)
              ·
                refine ⟨5820477117496803311425393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7760636156662404415233857 5820477117496803311425393)
                ·
                  refine ⟨4365357838122602483569045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5820477117496803311425393 4365357838122602483569045)
                  ·
                    refine ⟨204626148661996991417299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4365357838122602483569045 204626148661996991417299)
                    ·
                      rfl

theorem cell22_597762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_597762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597762 prefixEnd_597762 := by exact prefixLift 597762
  have htrace : WordTrace (prefixWord ++ tailWord_597762) baseStart_597762 baseEnd_597762 := by
    simpa [prefixWord, tailWord_597762, baseEnd_597762] using wordTrace_append hprefix tailTrace_597762
  have hstable : (prefixWord ++ tailWord_597762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597762).length < 2 ^ (prefixWord ++ tailWord_597762).sum := by decide
  have hdescent : baseEnd_597762 < baseStart_597762 := by decide
  rcases family_descends (prefixWord ++ tailWord_597762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597764 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_597764 : Nat := 118140960795 + 597764 * 2 ^ 59
def prefixEnd_597764 : Nat := 4983230072969 + 3 ^ 40 * 597764 * 2
def baseEnd_597764 : Nat := 204626833302869652867293

theorem tailTrace_597764 : CollatzResearch.WordTrace tailWord_597764 prefixEnd_597764 204626833302869652867293 := by
  unfold tailWord_597764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901122103205296404256173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14534829470940395205674897 10901122103205296404256173)
  ·
    refine ⟨4087920788701986151596065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10901122103205296404256173 4087920788701986151596065)
    ·
      refine ⟨3065940591526489613697049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4087920788701986151596065 3065940591526489613697049)
      ·
        refine ⟨2299455443644867210272787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3065940591526489613697049 2299455443644867210272787)
        ·
          refine ⟨3449183165467300815409181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299455443644867210272787 3449183165467300815409181)
          ·
            refine ⟨1293443687050237805778443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3449183165467300815409181 1293443687050237805778443)
            ·
              refine ⟨1940165530575356708667665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293443687050237805778443 1940165530575356708667665)
              ·
                refine ⟨1455124147931517531500749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940165530575356708667665 1455124147931517531500749)
                ·
                  refine ⟨545671555474319074312781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1455124147931517531500749 545671555474319074312781)
                  ·
                    refine ⟨204626833302869652867293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545671555474319074312781 204626833302869652867293)
                    ·
                      rfl

theorem cell22_597764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_597764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597764 prefixEnd_597764 := by exact prefixLift 597764
  have htrace : WordTrace (prefixWord ++ tailWord_597764) baseStart_597764 baseEnd_597764 := by
    simpa [prefixWord, tailWord_597764, baseEnd_597764] using wordTrace_append hprefix tailTrace_597764
  have hstable : (prefixWord ++ tailWord_597764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597764).length < 2 ^ (prefixWord ++ tailWord_597764).sum := by decide
  have hdescent : baseEnd_597764 < baseStart_597764 := by decide
  rcases family_descends (prefixWord ++ tailWord_597764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597781 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_597781 : Nat := 118140960795 + 597781 * 2 ^ 59
def prefixEnd_597781 : Nat := 4983230072969 + 3 ^ 40 * 597781 * 2
def baseEnd_597781 : Nat := 204632652750287275192241

theorem tailTrace_597781 : CollatzResearch.WordTrace tailWord_597781 prefixEnd_597781 204632652750287275192241 := by
  unfold tailWord_597781
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802864247349004711881197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14535242831566003141254131 21802864247349004711881197)
  ·
    refine ⟨8176074092755876766955449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21802864247349004711881197 8176074092755876766955449)
    ·
      refine ⟨6132055569566907575216587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8176074092755876766955449 6132055569566907575216587)
      ·
        refine ⟨9198083354350361362824881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6132055569566907575216587 9198083354350361362824881)
        ·
          refine ⟨6898562515762771022118661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9198083354350361362824881 6898562515762771022118661)
          ·
            refine ⟨1293480471705519566647249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6898562515762771022118661 1293480471705519566647249)
            ·
              refine ⟨970110353779139674985437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293480471705519566647249 970110353779139674985437)
              ·
                refine ⟨363791382667177378119539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970110353779139674985437 363791382667177378119539)
                ·
                  refine ⟨545687074000766067179309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363791382667177378119539 545687074000766067179309)
                  ·
                    refine ⟨204632652750287275192241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545687074000766067179309 204632652750287275192241)
                    ·
                      rfl

theorem cell22_597781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_597781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597781 prefixEnd_597781 := by exact prefixLift 597781
  have htrace : WordTrace (prefixWord ++ tailWord_597781) baseStart_597781 baseEnd_597781 := by
    simpa [prefixWord, tailWord_597781, baseEnd_597781] using wordTrace_append hprefix tailTrace_597781
  have hstable : (prefixWord ++ tailWord_597781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597781).length < 2 ^ (prefixWord ++ tailWord_597781).sum := by decide
  have hdescent : baseEnd_597781 < baseStart_597781 := by decide
  rcases family_descends (prefixWord ++ tailWord_597781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597856 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 4]
def baseStart_597856 : Nat := 118140960795 + 597856 * 2 ^ 59
def prefixEnd_597856 : Nat := 4983230072969 + 3 ^ 40 * 597856 * 2
def baseEnd_597856 : Nat := 68219442261004026522337

theorem tailTrace_597856 : CollatzResearch.WordTrace tailWord_597856 prefixEnd_597856 68219442261004026522337 := by
  unfold tailWord_597856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902799861038646260430711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14537066481384861680574281 10902799861038646260430711)
  ·
    refine ⟨16354199791557969390646067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10902799861038646260430711 16354199791557969390646067)
    ·
      refine ⟨24531299687336954085969101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16354199791557969390646067 24531299687336954085969101)
      ·
        refine ⟨9199237382751357782238413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24531299687336954085969101 9199237382751357782238413)
        ·
          refine ⟨3449714018531759168339405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9199237382751357782238413 3449714018531759168339405)
          ·
            refine ⟨1293642756949409688127277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3449714018531759168339405 1293642756949409688127277)
            ·
              refine ⟨485116033856028633047729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1293642756949409688127277 485116033856028633047729)
              ·
                refine ⟨363837025392021474785797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485116033856028633047729 363837025392021474785797)
                ·
                  refine ⟨68219442261004026522337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 363837025392021474785797 68219442261004026522337)
                  ·
                    rfl

theorem cell22_597856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_597856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597856 prefixEnd_597856 := by exact prefixLift 597856
  have htrace : WordTrace (prefixWord ++ tailWord_597856) baseStart_597856 baseEnd_597856 := by
    simpa [prefixWord, tailWord_597856, baseEnd_597856] using wordTrace_append hprefix tailTrace_597856
  have hstable : (prefixWord ++ tailWord_597856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597856).length < 2 ^ (prefixWord ++ tailWord_597856).sum := by decide
  have hdescent : baseEnd_597856 < baseStart_597856 := by decide
  rcases family_descends (prefixWord ++ tailWord_597856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597886 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_597886 : Nat := 118140960795 + 597886 * 2 ^ 59
def prefixEnd_597886 : Nat := 4983230072969 + 3 ^ 40 * 597886 * 2
def baseEnd_597886 : Nat := 204668596396102001316919

theorem tailTrace_597886 : CollatzResearch.WordTrace tailWord_597886 prefixEnd_597886 204668596396102001316919 := by
  unfold tailWord_597886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725836738996075955556689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14537795941312405096302341 2725836738996075955556689)
  ·
    refine ⟨2044377554247056966667517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2725836738996075955556689 2044377554247056966667517)
    ·
      refine ⟨766641582842646362500319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2044377554247056966667517 766641582842646362500319)
      ·
        refine ⟨1149962374263969543750479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766641582842646362500319 1149962374263969543750479)
        ·
          refine ⟨1724943561395954315625719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149962374263969543750479 1724943561395954315625719)
          ·
            refine ⟨2587415342093931473438579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724943561395954315625719 2587415342093931473438579)
            ·
              refine ⟨3881123013140897210157869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587415342093931473438579 3881123013140897210157869)
              ·
                refine ⟨1455421129927836453809201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3881123013140897210157869 1455421129927836453809201)
                ·
                  refine ⟨1091565847445877340356901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1455421129927836453809201 1091565847445877340356901)
                  ·
                    refine ⟨204668596396102001316919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1091565847445877340356901 204668596396102001316919)
                    ·
                      rfl

theorem cell22_597886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_597886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597886 prefixEnd_597886 := by exact prefixLift 597886
  have htrace : WordTrace (prefixWord ++ tailWord_597886) baseStart_597886 baseEnd_597886 := by
    simpa [prefixWord, tailWord_597886, baseEnd_597886] using wordTrace_append hprefix tailTrace_597886
  have hstable : (prefixWord ++ tailWord_597886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597886).length < 2 ^ (prefixWord ++ tailWord_597886).sum := by decide
  have hdescent : baseEnd_597886 < baseStart_597886 := by decide
  rcases family_descends (prefixWord ++ tailWord_597886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597918 : List Nat := [4, 3, 1, 3, 1, 2, 1, 7]
def baseStart_597918 : Nat := 118140960795 + 597918 * 2 ^ 59
def prefixEnd_597918 : Nat := 4983230072969 + 3 ^ 40 * 597918 * 2
def baseEnd_597918 : Nat := 22742172294451620501869

theorem tailTrace_597918 : CollatzResearch.WordTrace tailWord_597918 prefixEnd_597918 22742172294451620501869 := by
  unfold tailWord_597918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725982630981584638702301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14538574031901784739745605 2725982630981584638702301)
  ·
    refine ⟨1022243486618094239513363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2725982630981584638702301 1022243486618094239513363)
    ·
      refine ⟨1533365229927141359270045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022243486618094239513363 1533365229927141359270045)
      ·
        refine ⟨575011961222678009726267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1533365229927141359270045 575011961222678009726267)
        ·
          refine ⟨862517941834017014589401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575011961222678009726267 862517941834017014589401)
          ·
            refine ⟨646888456375512760942051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862517941834017014589401 646888456375512760942051)
            ·
              refine ⟨970332684563269141413077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646888456375512760942051 970332684563269141413077)
              ·
                refine ⟨22742172294451620501869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 970332684563269141413077 22742172294451620501869)
                ·
                  rfl

theorem cell22_597918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_597918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_597918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_597918 prefixEnd_597918 := by exact prefixLift 597918
  have htrace : WordTrace (prefixWord ++ tailWord_597918) baseStart_597918 baseEnd_597918 := by
    simpa [prefixWord, tailWord_597918, baseEnd_597918] using wordTrace_append hprefix tailTrace_597918
  have hstable : (prefixWord ++ tailWord_597918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597918).length < 2 ^ (prefixWord ++ tailWord_597918).sum := by decide
  have hdescent : baseEnd_597918 < baseStart_597918 := by decide
  rcases family_descends (prefixWord ++ tailWord_597918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598032 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_598032 : Nat := 118140960795 + 598032 * 2 ^ 59
def prefixEnd_598032 : Nat := 4983230072969 + 3 ^ 40 * 598032 * 2
def baseEnd_598032 : Nat := 204718575179806287166471

theorem tailTrace_598032 : CollatzResearch.WordTrace tailWord_598032 prefixEnd_598032 204718575179806287166471 := by
  unfold tailWord_598032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906009484719837289634175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14541345979626449719512233 10906009484719837289634175)
  ·
    refine ⟨16359014227079755934451263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10906009484719837289634175 16359014227079755934451263)
    ·
      refine ⟨24538521340619633901676895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16359014227079755934451263 24538521340619633901676895)
      ·
        refine ⟨36807782010929450852515343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24538521340619633901676895 36807782010929450852515343)
        ·
          refine ⟨55211673016394176278773015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36807782010929450852515343 55211673016394176278773015)
          ·
            refine ⟨82817509524591264418159523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55211673016394176278773015 82817509524591264418159523)
            ·
              refine ⟨124226264286886896627239285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82817509524591264418159523 124226264286886896627239285)
              ·
                refine ⟨11646212276895646558803683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124226264286886896627239285 11646212276895646558803683)
                ·
                  refine ⟨17469318415343469838205525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11646212276895646558803683 17469318415343469838205525)
                  ·
                    refine ⟨204718575179806287166471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17469318415343469838205525 204718575179806287166471)
                    ·
                      rfl

theorem cell22_598032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_598032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598032 prefixEnd_598032 := by exact prefixLift 598032
  have htrace : WordTrace (prefixWord ++ tailWord_598032) baseStart_598032 baseEnd_598032 := by
    simpa [prefixWord, tailWord_598032, baseEnd_598032] using wordTrace_append hprefix tailTrace_598032
  have hstable : (prefixWord ++ tailWord_598032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598032).length < 2 ^ (prefixWord ++ tailWord_598032).sum := by decide
  have hdescent : baseEnd_598032 < baseStart_598032 := by decide
  rcases family_descends (prefixWord ++ tailWord_598032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598081 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 5]
def baseStart_598081 : Nat := 118140960795 + 598081 * 2 ^ 59
def prefixEnd_598081 : Nat := 4983230072969 + 3 ^ 40 * 598081 * 2
def baseEnd_598081 : Nat := 68245116293728830897107

theorem tailTrace_598081 : CollatzResearch.WordTrace tailWord_598081 prefixEnd_598081 68245116293728830897107 := by
  unfold tailWord_598081
  simp only [CollatzResearch.WordTrace]
  refine ⟨21813806146262155947802097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14542537430841437298534731 21813806146262155947802097)
  ·
    refine ⟨16360354609696616960851573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21813806146262155947802097 16360354609696616960851573)
    ·
      refine ⟨1533783244659057840079835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16360354609696616960851573 1533783244659057840079835)
      ·
        refine ⟨2300674866988586760119753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533783244659057840079835 2300674866988586760119753)
        ·
          refine ⟨1725506150241440070089815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2300674866988586760119753 1725506150241440070089815)
          ·
            refine ⟨2588259225362160105134723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725506150241440070089815 2588259225362160105134723)
            ·
              refine ⟨3882388838043240157702085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588259225362160105134723 3882388838043240157702085)
              ·
                refine ⟨727947907133107529569141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3882388838043240157702085 727947907133107529569141)
                ·
                  refine ⟨68245116293728830897107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 727947907133107529569141 68245116293728830897107)
                  ·
                    rfl

theorem cell22_598081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_598081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598081 prefixEnd_598081 := by exact prefixLift 598081
  have htrace : WordTrace (prefixWord ++ tailWord_598081) baseStart_598081 baseEnd_598081 := by
    simpa [prefixWord, tailWord_598081, baseEnd_598081] using wordTrace_append hprefix tailTrace_598081
  have hstable : (prefixWord ++ tailWord_598081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598081).length < 2 ^ (prefixWord ++ tailWord_598081).sum := by decide
  have hdescent : baseEnd_598081 < baseStart_598081 := by decide
  rcases family_descends (prefixWord ++ tailWord_598081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598128 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 1, 4]
def baseStart_598128 : Nat := 118140960795 + 598128 * 2 ^ 59
def prefixEnd_598128 : Nat := 4983230072969 + 3 ^ 40 * 598128 * 2
def baseEnd_598128 : Nat := 204751437941694036766177

theorem tailTrace_598128 : CollatzResearch.WordTrace tailWord_598128 prefixEnd_598128 204751437941694036766177 := by
  unfold tailWord_598128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10907760188545941487381519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14543680251394588649842025 10907760188545941487381519)
  ·
    refine ⟨16361640282818912231072279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10907760188545941487381519 16361640282818912231072279)
    ·
      refine ⟨24542460424228368346608419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16361640282818912231072279 24542460424228368346608419)
      ·
        refine ⟨36813690636342552519912629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24542460424228368346608419 36813690636342552519912629)
        ·
          refine ⟨3451283497157114298741809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36813690636342552519912629 3451283497157114298741809)
          ·
            refine ⟨2588462622867835724056357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3451283497157114298741809 2588462622867835724056357)
            ·
              refine ⟨485336741787719198260567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2588462622867835724056357 485336741787719198260567)
              ·
                refine ⟨728005112681578797390851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485336741787719198260567 728005112681578797390851)
                ·
                  refine ⟨1092007669022368196086277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728005112681578797390851 1092007669022368196086277)
                  ·
                    refine ⟨204751437941694036766177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1092007669022368196086277 204751437941694036766177)
                    ·
                      rfl

theorem cell22_598128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_598128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598128 prefixEnd_598128 := by exact prefixLift 598128
  have htrace : WordTrace (prefixWord ++ tailWord_598128) baseStart_598128 baseEnd_598128 := by
    simpa [prefixWord, tailWord_598128, baseEnd_598128] using wordTrace_append hprefix tailTrace_598128
  have hstable : (prefixWord ++ tailWord_598128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598128).length < 2 ^ (prefixWord ++ tailWord_598128).sum := by decide
  have hdescent : baseEnd_598128 < baseStart_598128 := by decide
  rcases family_descends (prefixWord ++ tailWord_598128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598209 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 2, 3]
def baseStart_598209 : Nat := 118140960795 + 598209 * 2 ^ 59
def prefixEnd_598209 : Nat := 4983230072969 + 3 ^ 40 * 598209 * 2
def baseEnd_598209 : Nat := 204779165897036825490929

theorem tailTrace_598209 : CollatzResearch.WordTrace tailWord_598209 prefixEnd_598209 204779165897036825490929 := by
  unfold tailWord_598209
  simp only [CollatzResearch.WordTrace]
  refine ⟨21818474689798433808461681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14545649793198955872307787 21818474689798433808461681)
  ·
    refine ⟨16363856017348825356346261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21818474689798433808461681 16363856017348825356346261)
    ·
      refine ⟨767055750813226188578731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16363856017348825356346261 767055750813226188578731)
      ·
        refine ⟨1150583626219839282868097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767055750813226188578731 1150583626219839282868097)
        ·
          refine ⟨862937719664879462151073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150583626219839282868097 862937719664879462151073)
          ·
            refine ⟨647203289748659596613305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862937719664879462151073 647203289748659596613305)
            ·
              refine ⟨485402467311494697459979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647203289748659596613305 485402467311494697459979)
              ·
                refine ⟨728103700967242046189969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485402467311494697459979 728103700967242046189969)
                ·
                  refine ⟨546077775725431534642477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728103700967242046189969 546077775725431534642477)
                  ·
                    refine ⟨204779165897036825490929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546077775725431534642477 204779165897036825490929)
                    ·
                      rfl

theorem cell22_598209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_598209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598209 prefixEnd_598209 := by exact prefixLift 598209
  have htrace : WordTrace (prefixWord ++ tailWord_598209) baseStart_598209 baseEnd_598209 := by
    simpa [prefixWord, tailWord_598209, baseEnd_598209] using wordTrace_append hprefix tailTrace_598209
  have hstable : (prefixWord ++ tailWord_598209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598209).length < 2 ^ (prefixWord ++ tailWord_598209).sum := by decide
  have hdescent : baseEnd_598209 < baseStart_598209 := by decide
  rcases family_descends (prefixWord ++ tailWord_598209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598295 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 4]
def baseStart_598295 : Nat := 118140960795 + 598295 * 2 ^ 59
def prefixEnd_598295 : Nat := 4983230072969 + 3 ^ 40 * 598295 * 2
def baseEnd_598295 : Nat := 68269535151520422613555

theorem tailTrace_598295 : CollatzResearch.WordTrace tailWord_598295 prefixEnd_598295 68269535151520422613555 := by
  unfold tailWord_598295
  simp only [CollatzResearch.WordTrace]
  refine ⟨21821611367486870496092339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14547740911657913664061559 21821611367486870496092339)
  ·
    refine ⟨32732417051230305744138509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21821611367486870496092339 32732417051230305744138509)
    ·
      refine ⟨12274656394211364654051941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32732417051230305744138509 12274656394211364654051941)
      ·
        refine ⟨2301498073914630872634739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12274656394211364654051941 2301498073914630872634739)
        ·
          refine ⟨3452247110871946308952109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301498073914630872634739 3452247110871946308952109)
          ·
            refine ⟨1294592666576979865857041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3452247110871946308952109 1294592666576979865857041)
            ·
              refine ⟨970944499932734899392781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294592666576979865857041 970944499932734899392781)
              ·
                refine ⟨364104187474775587272293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970944499932734899392781 364104187474775587272293)
                ·
                  refine ⟨68269535151520422613555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364104187474775587272293 68269535151520422613555)
                  ·
                    rfl

theorem cell22_598295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 4].length) (baseStart_598295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598295 prefixEnd_598295 := by exact prefixLift 598295
  have htrace : WordTrace (prefixWord ++ tailWord_598295) baseStart_598295 baseEnd_598295 := by
    simpa [prefixWord, tailWord_598295, baseEnd_598295] using wordTrace_append hprefix tailTrace_598295
  have hstable : (prefixWord ++ tailWord_598295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598295).length < 2 ^ (prefixWord ++ tailWord_598295).sum := by decide
  have hdescent : baseEnd_598295 < baseStart_598295 := by decide
  rcases family_descends (prefixWord ++ tailWord_598295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598340 : List Nat := [2, 3, 4, 1, 2, 1, 1, 8]
def baseStart_598340 : Nat := 118140960795 + 598340 * 2 ^ 59
def prefixEnd_598340 : Nat := 4983230072969 + 3 ^ 40 * 598340 * 2
def baseEnd_598340 : Nat := 22758223319355127829503

theorem tailTrace_598340 : CollatzResearch.WordTrace tailWord_598340 prefixEnd_598340 22758223319355127829503 := by
  unfold tailWord_598340
  simp only [CollatzResearch.WordTrace]
  refine ⟨10911626326161921590740237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14548835101549228787653649 10911626326161921590740237)
  ·
    refine ⟨4091859872310720596527589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10911626326161921590740237 4091859872310720596527589)
    ·
      refine ⟨767223726058260111848923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4091859872310720596527589 767223726058260111848923)
      ·
        refine ⟨1150835589087390167773385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767223726058260111848923 1150835589087390167773385)
        ·
          refine ⟨863126691815542625830039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150835589087390167773385 863126691815542625830039)
          ·
            refine ⟨1294690037723313938745059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863126691815542625830039 1294690037723313938745059)
            ·
              refine ⟨1942035056584970908117589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294690037723313938745059 1942035056584970908117589)
              ·
                refine ⟨22758223319355127829503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1942035056584970908117589 22758223319355127829503)
                ·
                  rfl

theorem cell22_598340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_598340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598340 prefixEnd_598340 := by exact prefixLift 598340
  have htrace : WordTrace (prefixWord ++ tailWord_598340) baseStart_598340 baseEnd_598340 := by
    simpa [prefixWord, tailWord_598340, baseEnd_598340] using wordTrace_append hprefix tailTrace_598340
  have hstable : (prefixWord ++ tailWord_598340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598340).length < 2 ^ (prefixWord ++ tailWord_598340).sum := by decide
  have hdescent : baseEnd_598340 < baseStart_598340 := by decide
  rcases family_descends (prefixWord ++ tailWord_598340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598355 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 1, 3]
def baseStart_598355 : Nat := 118140960795 + 598355 * 2 ^ 59
def prefixEnd_598355 : Nat := 4983230072969 + 3 ^ 40 * 598355 * 2
def baseEnd_598355 : Nat := 204829144680741111340481

theorem tailTrace_598355 : CollatzResearch.WordTrace tailWord_598355 prefixEnd_598355 204829144680741111340481 := by
  unfold tailWord_598355
  simp only [CollatzResearch.WordTrace]
  refine ⟨21823799747269500743276519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14549199831513000495517679 21823799747269500743276519)
  ·
    refine ⟨32735699620904251114914779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21823799747269500743276519 32735699620904251114914779)
    ·
      refine ⟨49103549431356376672372169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32735699620904251114914779 49103549431356376672372169)
      ·
        refine ⟨36827662073517282504279127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49103549431356376672372169 36827662073517282504279127)
        ·
          refine ⟨55241493110275923756418691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36827662073517282504279127 55241493110275923756418691)
          ·
            refine ⟨82862239665413885634628037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55241493110275923756418691 82862239665413885634628037)
            ·
              refine ⟨15536669937265103556492757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82862239665413885634628037 15536669937265103556492757)
              ·
                refine ⟨364140701654650864605299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15536669937265103556492757 364140701654650864605299)
                ·
                  refine ⟨546211052481976296907949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364140701654650864605299 546211052481976296907949)
                  ·
                    refine ⟨204829144680741111340481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546211052481976296907949 204829144680741111340481)
                    ·
                      rfl

theorem cell22_598355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 3].length) (baseStart_598355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598355 prefixEnd_598355 := by exact prefixLift 598355
  have htrace : WordTrace (prefixWord ++ tailWord_598355) baseStart_598355 baseEnd_598355 := by
    simpa [prefixWord, tailWord_598355, baseEnd_598355] using wordTrace_append hprefix tailTrace_598355
  have hstable : (prefixWord ++ tailWord_598355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598355).length < 2 ^ (prefixWord ++ tailWord_598355).sum := by decide
  have hdescent : baseEnd_598355 < baseStart_598355 := by decide
  rcases family_descends (prefixWord ++ tailWord_598355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598460 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_598460 : Nat := 118140960795 + 598460 * 2 ^ 59
def prefixEnd_598460 : Nat := 4983230072969 + 3 ^ 40 * 598460 * 2
def baseEnd_598460 : Nat := 204865088326555837465159

theorem tailTrace_598460 : CollatzResearch.WordTrace tailWord_598460 prefixEnd_598460 204865088326555837465159 := by
  unfold tailWord_598460
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913814705944551837924417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14551752941259402450565889 10913814705944551837924417)
  ·
    refine ⟨8185361029458413878443313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10913814705944551837924417 8185361029458413878443313)
    ·
      refine ⟨6139020772093810408832485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8185361029458413878443313 6139020772093810408832485)
      ·
        refine ⟨1151066394767589451656091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6139020772093810408832485 1151066394767589451656091)
        ·
          refine ⟨1726599592151384177484137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151066394767589451656091 1726599592151384177484137)
          ·
            refine ⟨1294949694113538133113103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1726599592151384177484137 1294949694113538133113103)
            ·
              refine ⟨1942424541170307199669655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294949694113538133113103 1942424541170307199669655)
              ·
                refine ⟨2913636811755460799504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1942424541170307199669655 2913636811755460799504483)
                ·
                  refine ⟨4370455217633191199256725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913636811755460799504483 4370455217633191199256725)
                  ·
                    refine ⟨204865088326555837465159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4370455217633191199256725 204865088326555837465159)
                    ·
                      rfl

theorem cell22_598460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_598460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598460 prefixEnd_598460 := by exact prefixLift 598460
  have htrace : WordTrace (prefixWord ++ tailWord_598460) baseStart_598460 baseEnd_598460 := by
    simpa [prefixWord, tailWord_598460, baseEnd_598460] using wordTrace_append hprefix tailTrace_598460
  have hstable : (prefixWord ++ tailWord_598460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598460).length < 2 ^ (prefixWord ++ tailWord_598460).sum := by decide
  have hdescent : baseEnd_598460 < baseStart_598460 := by decide
  rcases family_descends (prefixWord ++ tailWord_598460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598541 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_598541 : Nat := 118140960795 + 598541 * 2 ^ 59
def prefixEnd_598541 : Nat := 4983230072969 + 3 ^ 40 * 598541 * 2
def baseEnd_598541 : Nat := 204892816281898626189911

theorem tailTrace_598541 : CollatzResearch.WordTrace tailWord_598541 prefixEnd_598541 204892816281898626189911 := by
  unfold tailWord_598541
  simp only [CollatzResearch.WordTrace]
  refine ⟨21830583724595654509547477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14553722483063769673031651 21830583724595654509547477)
  ·
    refine ⟨511654306045210652567519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 21830583724595654509547477 511654306045210652567519)
    ·
      refine ⟨767481459067815978851279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511654306045210652567519 767481459067815978851279)
      ·
        refine ⟨1151222188601723968276919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767481459067815978851279 1151222188601723968276919)
        ·
          refine ⟨1726833282902585952415379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151222188601723968276919 1726833282902585952415379)
          ·
            refine ⟨2590249924353878928623069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726833282902585952415379 2590249924353878928623069)
            ·
              refine ⟨971343721632704598233651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2590249924353878928623069 971343721632704598233651)
              ·
                refine ⟨1457015582449056897350477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971343721632704598233651 1457015582449056897350477)
                ·
                  refine ⟨546380843418396336506429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1457015582449056897350477 546380843418396336506429)
                  ·
                    refine ⟨204892816281898626189911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546380843418396336506429 204892816281898626189911)
                    ·
                      rfl

theorem cell22_598541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_598541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598541 prefixEnd_598541 := by exact prefixLift 598541
  have htrace : WordTrace (prefixWord ++ tailWord_598541) baseStart_598541 baseEnd_598541 := by
    simpa [prefixWord, tailWord_598541, baseEnd_598541] using wordTrace_append hprefix tailTrace_598541
  have hstable : (prefixWord ++ tailWord_598541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598541).length < 2 ^ (prefixWord ++ tailWord_598541).sum := by decide
  have hdescent : baseEnd_598541 < baseStart_598541 := by decide
  rcases family_descends (prefixWord ++ tailWord_598541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598597 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_598597 : Nat := 118140960795 + 598597 * 2 ^ 59
def prefixEnd_598597 : Nat := 4983230072969 + 3 ^ 40 * 598597 * 2
def baseEnd_598597 : Nat := 204911986226333146789739

theorem tailTrace_598597 : CollatzResearch.WordTrace tailWord_598597 prefixEnd_598597 204911986226333146789739 := by
  unfold tailWord_598597
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832626212392776073586045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14555084141595184049057363 21832626212392776073586045)
  ·
    refine ⟨8187234829647291027594767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21832626212392776073586045 8187234829647291027594767)
    ·
      refine ⟨12280852244470936541392151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8187234829647291027594767 12280852244470936541392151)
      ·
        refine ⟨18421278366706404812088227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280852244470936541392151 18421278366706404812088227)
        ·
          refine ⟨27631917550059607218132341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18421278366706404812088227 27631917550059607218132341)
          ·
            refine ⟨2590492270318088176699907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27631917550059607218132341 2590492270318088176699907)
            ·
              refine ⟨3885738405477132265049861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590492270318088176699907 3885738405477132265049861)
              ·
                refine ⟨728575951026962299696849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3885738405477132265049861 728575951026962299696849)
                ·
                  refine ⟨546431963270221724772637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728575951026962299696849 546431963270221724772637)
                  ·
                    refine ⟨204911986226333146789739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546431963270221724772637 204911986226333146789739)
                    ·
                      rfl

theorem cell22_598597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_598597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598597 prefixEnd_598597 := by exact prefixLift 598597
  have htrace : WordTrace (prefixWord ++ tailWord_598597) baseStart_598597 baseEnd_598597 := by
    simpa [prefixWord, tailWord_598597, baseEnd_598597] using wordTrace_append hprefix tailTrace_598597
  have hstable : (prefixWord ++ tailWord_598597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598597).length < 2 ^ (prefixWord ++ tailWord_598597).sum := by decide
  have hdescent : baseEnd_598597 < baseStart_598597 := by decide
  rcases family_descends (prefixWord ++ tailWord_598597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598599 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 4]
def baseStart_598599 : Nat := 118140960795 + 598599 * 2 ^ 59
def prefixEnd_598599 : Nat := 4983230072969 + 3 ^ 40 * 598599 * 2
def baseEnd_598599 : Nat := 68304223622401936079911

theorem tailTrace_598599 : CollatzResearch.WordTrace tailWord_598599 prefixEnd_598599 68304223622401936079911 := by
  unfold tailWord_598599
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832699158385530415158851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14555132772257020276772567 21832699158385530415158851)
  ·
    refine ⟨32749048737578295622738277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21832699158385530415158851 32749048737578295622738277)
    ·
      refine ⟨6140446638295930429263427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32749048737578295622738277 6140446638295930429263427)
      ·
        refine ⟨9210669957443895643895141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6140446638295930429263427 9210669957443895643895141)
        ·
          refine ⟨1727000617020730433230339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9210669957443895643895141 1727000617020730433230339)
          ·
            refine ⟨2590500925531095649845509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727000617020730433230339 2590500925531095649845509)
            ·
              refine ⟨485718923537080434346033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2590500925531095649845509 485718923537080434346033)
              ·
                refine ⟨364289192652810325759525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485718923537080434346033 364289192652810325759525)
                ·
                  refine ⟨68304223622401936079911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364289192652810325759525 68304223622401936079911)
                  ·
                    rfl

theorem cell22_598599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 4].length) (baseStart_598599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598599 prefixEnd_598599 := by exact prefixLift 598599
  have htrace : WordTrace (prefixWord ++ tailWord_598599) baseStart_598599 baseEnd_598599 := by
    simpa [prefixWord, tailWord_598599, baseEnd_598599] using wordTrace_append hprefix tailTrace_598599
  have hstable : (prefixWord ++ tailWord_598599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598599).length < 2 ^ (prefixWord ++ tailWord_598599).sum := by decide
  have hdescent : baseEnd_598599 < baseStart_598599 := by decide
  rcases family_descends (prefixWord ++ tailWord_598599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598629 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_598629 : Nat := 118140960795 + 598629 * 2 ^ 59
def prefixEnd_598629 : Nat := 4983230072969 + 3 ^ 40 * 598629 * 2
def baseEnd_598629 : Nat := 204922940480295729989641

theorem tailTrace_598629 : CollatzResearch.WordTrace tailWord_598629 prefixEnd_598629 204922940480295729989641 := by
  unfold tailWord_598629
  simp only [CollatzResearch.WordTrace]
  refine ⟨21833793348276845538750941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14555862232184563692500627 21833793348276845538750941)
  ·
    refine ⟨8187672505603817077031603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21833793348276845538750941 8187672505603817077031603)
    ·
      refine ⟨12281508758405725615547405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8187672505603817077031603 12281508758405725615547405)
      ·
        refine ⟨4605565784402147105830277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12281508758405725615547405 4605565784402147105830277)
        ·
          refine ⟨863543584575402582343177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4605565784402147105830277 863543584575402582343177)
          ·
            refine ⟨647657688431551936757383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863543584575402582343177 647657688431551936757383)
            ·
              refine ⟨971486532647327905136075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647657688431551936757383 971486532647327905136075)
              ·
                refine ⟨1457229798970991857704113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971486532647327905136075 1457229798970991857704113)
                ·
                  refine ⟨1092922349228243893278085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457229798970991857704113 1092922349228243893278085)
                  ·
                    refine ⟨204922940480295729989641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1092922349228243893278085 204922940480295729989641)
                    ·
                      rfl

theorem cell22_598629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_598629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598629 prefixEnd_598629 := by exact prefixLift 598629
  have htrace : WordTrace (prefixWord ++ tailWord_598629) baseStart_598629 baseEnd_598629 := by
    simpa [prefixWord, tailWord_598629, baseEnd_598629] using wordTrace_append hprefix tailTrace_598629
  have hstable : (prefixWord ++ tailWord_598629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598629).length < 2 ^ (prefixWord ++ tailWord_598629).sum := by decide
  have hdescent : baseEnd_598629 < baseStart_598629 := by decide
  rcases family_descends (prefixWord ++ tailWord_598629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598655 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 5]
def baseStart_598655 : Nat := 118140960795 + 598655 * 2 ^ 59
def prefixEnd_598655 : Nat := 4983230072969 + 3 ^ 40 * 598655 * 2
def baseEnd_598655 : Nat := 68310613603880109613187

theorem tailTrace_598655 : CollatzResearch.WordTrace tailWord_598655 prefixEnd_598655 68310613603880109613187 := by
  unfold tailWord_598655
  simp only [CollatzResearch.WordTrace]
  refine ⟨21834741646182651979197419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14556494430788434652798279 21834741646182651979197419)
  ·
    refine ⟨32752112469273977968796129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21834741646182651979197419 32752112469273977968796129)
    ·
      refine ⟨24564084351955483476597097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32752112469273977968796129 24564084351955483476597097)
      ·
        refine ⟨18423063263966612607447823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24564084351955483476597097 18423063263966612607447823)
        ·
          refine ⟨27634594895949918911171735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18423063263966612607447823 27634594895949918911171735)
          ·
            refine ⟨41451892343924878366757603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27634594895949918911171735 41451892343924878366757603)
            ·
              refine ⟨62177838515887317550136405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41451892343924878366757603 62177838515887317550136405)
              ·
                refine ⟨728646545108054502540661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 62177838515887317550136405 728646545108054502540661)
                ·
                  refine ⟨68310613603880109613187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 728646545108054502540661 68310613603880109613187)
                  ·
                    rfl

theorem cell22_598655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 5].length) (baseStart_598655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598655 prefixEnd_598655 := by exact prefixLift 598655
  have htrace : WordTrace (prefixWord ++ tailWord_598655) baseStart_598655 baseEnd_598655 := by
    simpa [prefixWord, tailWord_598655, baseEnd_598655] using wordTrace_append hprefix tailTrace_598655
  have hstable : (prefixWord ++ tailWord_598655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598655).length < 2 ^ (prefixWord ++ tailWord_598655).sum := by decide
  have hdescent : baseEnd_598655 < baseStart_598655 := by decide
  rcases family_descends (prefixWord ++ tailWord_598655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598659 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 1, 3]
def baseStart_598659 : Nat := 118140960795 + 598659 * 2 ^ 59
def prefixEnd_598659 : Nat := 4983230072969 + 3 ^ 40 * 598659 * 2
def baseEnd_598659 : Nat := 204933210093385651739549

theorem tailTrace_598659 : CollatzResearch.WordTrace tailWord_598659 prefixEnd_598659 204933210093385651739549 := by
  unfold tailWord_598659
  simp only [CollatzResearch.WordTrace]
  refine ⟨21834887538168160662343031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14556591692112107108228687 21834887538168160662343031)
  ·
    refine ⟨32752331307252240993514547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21834887538168160662343031 32752331307252240993514547)
    ·
      refine ⟨49128496960878361490271821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32752331307252240993514547 49128496960878361490271821)
      ·
        refine ⟨18423186360329385558851933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49128496960878361490271821 18423186360329385558851933)
        ·
          refine ⟨6908694885123519584569475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18423186360329385558851933 6908694885123519584569475)
          ·
            refine ⟨10363042327685279376854213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6908694885123519584569475 10363042327685279376854213)
            ·
              refine ⟨1943070436440989883160165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10363042327685279376854213 1943070436440989883160165)
              ·
                refine ⟨364325706832685603092531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1943070436440989883160165 364325706832685603092531)
                ·
                  refine ⟨546488560249028404638797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364325706832685603092531 546488560249028404638797)
                  ·
                    refine ⟨204933210093385651739549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546488560249028404638797 204933210093385651739549)
                    ·
                      rfl

theorem cell22_598659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 3].length) (baseStart_598659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598659 prefixEnd_598659 := by exact prefixLift 598659
  have htrace : WordTrace (prefixWord ++ tailWord_598659) baseStart_598659 baseEnd_598659 := by
    simpa [prefixWord, tailWord_598659, baseEnd_598659] using wordTrace_append hprefix tailTrace_598659
  have hstable : (prefixWord ++ tailWord_598659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598659).length < 2 ^ (prefixWord ++ tailWord_598659).sum := by decide
  have hdescent : baseEnd_598659 < baseStart_598659 := by decide
  rcases family_descends (prefixWord ++ tailWord_598659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598710 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_598710 : Nat := 118140960795 + 598710 * 2 ^ 59
def prefixEnd_598710 : Nat := 4983230072969 + 3 ^ 40 * 598710 * 2
def baseEnd_598710 : Nat := 204950668435638518714393

theorem tailTrace_598710 : CollatzResearch.WordTrace tailWord_598710 prefixEnd_598710 204950668435638518714393 := by
  unfold tailWord_598710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364796728811462273278099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14557831773988930914966389 1364796728811462273278099)
  ·
    refine ⟨2047195093217193409917149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364796728811462273278099 2047195093217193409917149)
    ·
      refine ⟨767698159956447528718931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2047195093217193409917149 767698159956447528718931)
      ·
        refine ⟨1151547239934671293078397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767698159956447528718931 1151547239934671293078397)
        ·
          refine ⟨431830214975501734904399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1151547239934671293078397 431830214975501734904399)
          ·
            refine ⟨647745322463252602356599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431830214975501734904399 647745322463252602356599)
            ·
              refine ⟨971617983694878903534899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647745322463252602356599 971617983694878903534899)
              ·
                refine ⟨1457426975542318355302349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971617983694878903534899 1457426975542318355302349)
                ·
                  refine ⟨546535115828369383238381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1457426975542318355302349 546535115828369383238381)
                  ·
                    refine ⟨204950668435638518714393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546535115828369383238381 204950668435638518714393)
                    ·
                      rfl

theorem cell22_598710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_598710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598710 prefixEnd_598710 := by exact prefixLift 598710
  have htrace : WordTrace (prefixWord ++ tailWord_598710) baseStart_598710 baseEnd_598710 := by
    simpa [prefixWord, tailWord_598710, baseEnd_598710] using wordTrace_append hprefix tailTrace_598710
  have hstable : (prefixWord ++ tailWord_598710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598710).length < 2 ^ (prefixWord ++ tailWord_598710).sum := by decide
  have hdescent : baseEnd_598710 < baseStart_598710 := by decide
  rcases family_descends (prefixWord ++ tailWord_598710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598717 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 6]
def baseStart_598717 : Nat := 118140960795 + 598717 * 2 ^ 59
def prefixEnd_598717 : Nat := 4983230072969 + 3 ^ 40 * 598717 * 2
def baseEnd_598717 : Nat := 68317688226230944596457

theorem tailTrace_598717 : CollatzResearch.WordTrace tailWord_598717 prefixEnd_598717 68317688226230944596457 := by
  unfold tailWord_598717
  simp only [CollatzResearch.WordTrace]
  refine ⟨21837002971958036567954405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14558001981305357711969603 21837002971958036567954405)
  ·
    refine ⟨4094438057242131856491451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21837002971958036567954405 4094438057242131856491451)
    ·
      refine ⟨6141657085863197784737177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094438057242131856491451 6141657085863197784737177)
      ·
        refine ⟨4606242814397398338552883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6141657085863197784737177 4606242814397398338552883)
        ·
          refine ⟨6909364221596097507829325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606242814397398338552883 6909364221596097507829325)
          ·
            refine ⟨2591011583098536565435997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6909364221596097507829325 2591011583098536565435997)
            ·
              refine ⟨971629343661951212038499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2591011583098536565435997 971629343661951212038499)
              ·
                refine ⟨1457444015492926818057749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971629343661951212038499 1457444015492926818057749)
                ·
                  refine ⟨68317688226230944596457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1457444015492926818057749 68317688226230944596457)
                  ·
                    rfl

theorem cell22_598717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_598717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598717 prefixEnd_598717 := by exact prefixLift 598717
  have htrace : WordTrace (prefixWord ++ tailWord_598717) baseStart_598717 baseEnd_598717 := by
    simpa [prefixWord, tailWord_598717, baseEnd_598717] using wordTrace_append hprefix tailTrace_598717
  have hstable : (prefixWord ++ tailWord_598717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598717).length < 2 ^ (prefixWord ++ tailWord_598717).sum := by decide
  have hdescent : baseEnd_598717 < baseStart_598717 := by decide
  rcases family_descends (prefixWord ++ tailWord_598717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598745 : List Nat := [1, 2, 1, 2, 3, 2, 1, 10]
def baseStart_598745 : Nat := 118140960795 + 598745 * 2 ^ 59
def prefixEnd_598745 : Nat := 4983230072969 + 3 ^ 40 * 598745 * 2
def baseEnd_598745 : Nat := 22773627738990010454365

theorem tailTrace_598745 : CollatzResearch.WordTrace tailWord_598745 prefixEnd_598745 22773627738990010454365 := by
  unfold tailWord_598745
  simp only [CollatzResearch.WordTrace]
  refine ⟨21838024215856597349973689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14558682810571064899982459 21838024215856597349973689)
  ·
    refine ⟨16378518161892448012480267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21838024215856597349973689 16378518161892448012480267)
    ·
      refine ⟨24567777242838672018720401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16378518161892448012480267 24567777242838672018720401)
      ·
        refine ⟨18425832932129004014040301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24567777242838672018720401 18425832932129004014040301)
        ·
          refine ⟨6909687349548376505265113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18425832932129004014040301 6909687349548376505265113)
          ·
            refine ⟨5182265512161282378948835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6909687349548376505265113 5182265512161282378948835)
            ·
              refine ⟨7773398268241923568423253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182265512161282378948835 7773398268241923568423253)
              ·
                refine ⟨22773627738990010454365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7773398268241923568423253 22773627738990010454365)
                ·
                  rfl

theorem cell22_598745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 10].length) (baseStart_598745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598745 prefixEnd_598745 := by exact prefixLift 598745
  have htrace : WordTrace (prefixWord ++ tailWord_598745) baseStart_598745 baseEnd_598745 := by
    simpa [prefixWord, tailWord_598745, baseEnd_598745] using wordTrace_append hprefix tailTrace_598745
  have hstable : (prefixWord ++ tailWord_598745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598745).length < 2 ^ (prefixWord ++ tailWord_598745).sum := by decide
  have hdescent : baseEnd_598745 < baseStart_598745 := by decide
  rcases family_descends (prefixWord ++ tailWord_598745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598766 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_598766 : Nat := 118140960795 + 598766 * 2 ^ 59
def prefixEnd_598766 : Nat := 4983230072969 + 3 ^ 40 * 598766 * 2
def baseEnd_598766 : Nat := 204969838380073039314221

theorem tailTrace_598766 : CollatzResearch.WordTrace tailWord_598766 prefixEnd_598766 204969838380073039314221 := by
  unfold tailWord_598766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729848768597564742061019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14559193432520345290992101 2729848768597564742061019)
  ·
    refine ⟨4094773152896347113091529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729848768597564742061019 4094773152896347113091529)
    ·
      refine ⟨3071079864672260334818647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4094773152896347113091529 3071079864672260334818647)
      ·
        refine ⟨4606619797008390502227971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071079864672260334818647 4606619797008390502227971)
        ·
          refine ⟨6909929695512585753341957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606619797008390502227971 6909929695512585753341957)
          ·
            refine ⟨1295611817908609828751617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6909929695512585753341957 1295611817908609828751617)
            ·
              refine ⟨971708863431457371563713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295611817908609828751617 971708863431457371563713)
              ·
                refine ⟨728781647573593028672785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971708863431457371563713 728781647573593028672785)
                ·
                  refine ⟨546586235680194771504589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728781647573593028672785 546586235680194771504589)
                  ·
                    refine ⟨204969838380073039314221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546586235680194771504589 204969838380073039314221)
                    ·
                      rfl

theorem cell22_598766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_598766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598766 prefixEnd_598766 := by exact prefixLift 598766
  have htrace : WordTrace (prefixWord ++ tailWord_598766) baseStart_598766 baseEnd_598766 := by
    simpa [prefixWord, tailWord_598766, baseEnd_598766] using wordTrace_append hprefix tailTrace_598766
  have hstable : (prefixWord ++ tailWord_598766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598766).length < 2 ^ (prefixWord ++ tailWord_598766).sum := by decide
  have hdescent : baseEnd_598766 < baseStart_598766 := by decide
  rcases family_descends (prefixWord ++ tailWord_598766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598777 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_598777 : Nat := 118140960795 + 598777 * 2 ^ 59
def prefixEnd_598777 : Nat := 4983230072969 + 3 ^ 40 * 598777 * 2
def baseEnd_598777 : Nat := 204973603904872677289187

theorem tailTrace_598777 : CollatzResearch.WordTrace tailWord_598777 prefixEnd_598777 204973603904872677289187 := by
  unfold tailWord_598777
  simp only [CollatzResearch.WordTrace]
  refine ⟨21839191351740666815138585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14559460901160444543425723 21839191351740666815138585)
  ·
    refine ⟨16379393513805500111353939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21839191351740666815138585 16379393513805500111353939)
    ·
      refine ⟨24569090270708250167030909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16379393513805500111353939 24569090270708250167030909)
      ·
        refine ⟨9213408851515593812636591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24569090270708250167030909 9213408851515593812636591)
        ·
          refine ⟨13820113277273390718954887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9213408851515593812636591 13820113277273390718954887)
          ·
            refine ⟨20730169915910086078432331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13820113277273390718954887 20730169915910086078432331)
            ·
              refine ⟨31095254873865129117648497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20730169915910086078432331 31095254873865129117648497)
              ·
                refine ⟨23321441155398846838236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31095254873865129117648497 23321441155398846838236373)
                ·
                  refine ⟨546596277079660472771165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23321441155398846838236373 546596277079660472771165)
                  ·
                    refine ⟨204973603904872677289187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546596277079660472771165 204973603904872677289187)
                    ·
                      rfl

theorem cell22_598777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_598777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598777 prefixEnd_598777 := by exact prefixLift 598777
  have htrace : WordTrace (prefixWord ++ tailWord_598777) baseStart_598777 baseEnd_598777 := by
    simpa [prefixWord, tailWord_598777, baseEnd_598777] using wordTrace_append hprefix tailTrace_598777
  have hstable : (prefixWord ++ tailWord_598777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598777).length < 2 ^ (prefixWord ++ tailWord_598777).sum := by decide
  have hdescent : baseEnd_598777 < baseStart_598777 := by decide
  rcases family_descends (prefixWord ++ tailWord_598777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598794 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_598794 : Nat := 118140960795 + 598794 * 2 ^ 59
def prefixEnd_598794 : Nat := 4983230072969 + 3 ^ 40 * 598794 * 2
def baseEnd_598794 : Nat := 204979423352290299614135

theorem tailTrace_598794 : CollatzResearch.WordTrace tailWord_598794 prefixEnd_598794 204979423352290299614135 := by
  unfold tailWord_598794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459952848169769679626859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14559874261786052479004957 5459952848169769679626859)
  ·
    refine ⟨8189929272254654519440289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459952848169769679626859 8189929272254654519440289)
    ·
      refine ⟨6142446954190990889580217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8189929272254654519440289 6142446954190990889580217)
      ·
        refine ⟨4606835215643243167185163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6142446954190990889580217 4606835215643243167185163)
        ·
          refine ⟨6910252823464864750777745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606835215643243167185163 6910252823464864750777745)
          ·
            refine ⟨5182689617598648563083309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6910252823464864750777745 5182689617598648563083309)
            ·
              refine ⟨1943508606599493211156241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5182689617598648563083309 1943508606599493211156241)
              ·
                refine ⟨1457631454949619908367181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943508606599493211156241 1457631454949619908367181)
                ·
                  refine ⟨546611795606107465637693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1457631454949619908367181 546611795606107465637693)
                  ·
                    refine ⟨204979423352290299614135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546611795606107465637693 204979423352290299614135)
                    ·
                      rfl

theorem cell22_598794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_598794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598794 prefixEnd_598794 := by exact prefixLift 598794
  have htrace : WordTrace (prefixWord ++ tailWord_598794) baseStart_598794 baseEnd_598794 := by
    simpa [prefixWord, tailWord_598794, baseEnd_598794] using wordTrace_append hprefix tailTrace_598794
  have hstable : (prefixWord ++ tailWord_598794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598794).length < 2 ^ (prefixWord ++ tailWord_598794).sum := by decide
  have hdescent : baseEnd_598794 < baseStart_598794 := by decide
  rcases family_descends (prefixWord ++ tailWord_598794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598867 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 1, 5]
def baseStart_598867 : Nat := 118140960795 + 598867 * 2 ^ 59
def prefixEnd_598867 : Nat := 4983230072969 + 3 ^ 40 * 598867 * 2
def baseEnd_598867 : Nat := 205004412744142442538911

theorem tailTrace_598867 : CollatzResearch.WordTrace tailWord_598867 prefixEnd_598867 205004412744142442538911 := by
  unfold tailWord_598867
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842473921414612185914855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14561649280943074790609903 21842473921414612185914855)
  ·
    refine ⟨32763710882121918278872283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21842473921414612185914855 32763710882121918278872283)
    ·
      refine ⟨49145566323182877418308425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32763710882121918278872283 49145566323182877418308425)
      ·
        refine ⟨36859174742387158063731319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49145566323182877418308425 36859174742387158063731319)
        ·
          refine ⟨55288762113580737095596979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36859174742387158063731319 55288762113580737095596979)
          ·
            refine ⟨82933143170371105643395469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55288762113580737095596979 82933143170371105643395469)
            ·
              refine ⟨31099928688889164616273301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82933143170371105643395469 31099928688889164616273301)
              ·
                refine ⟨1457809157291679591387811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31099928688889164616273301 1457809157291679591387811)
                ·
                  refine ⟨2186713735937519387081717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457809157291679591387811 2186713735937519387081717)
                  ·
                    refine ⟨205004412744142442538911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2186713735937519387081717 205004412744142442538911)
                    ·
                      rfl

theorem cell22_598867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_598867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598867 prefixEnd_598867 := by exact prefixLift 598867
  have htrace : WordTrace (prefixWord ++ tailWord_598867) baseStart_598867 baseEnd_598867 := by
    simpa [prefixWord, tailWord_598867, baseEnd_598867] using wordTrace_append hprefix tailTrace_598867
  have hstable : (prefixWord ++ tailWord_598867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598867).length < 2 ^ (prefixWord ++ tailWord_598867).sum := by decide
  have hdescent : baseEnd_598867 < baseStart_598867 := by decide
  rcases family_descends (prefixWord ++ tailWord_598867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598897 : List Nat := [1, 2, 2, 2, 1, 4, 1, 9]
def baseStart_598897 : Nat := 118140960795 + 598897 * 2 ^ 59
def prefixEnd_598897 : Nat := 4983230072969 + 3 ^ 40 * 598897 * 2
def baseEnd_598897 : Nat := 22779409150803596032091

theorem tailTrace_598897 : CollatzResearch.WordTrace tailWord_598897 prefixEnd_598897 22779409150803596032091 := by
  unfold tailWord_598897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21843568111305927309506945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14562378740870618206337963 21843568111305927309506945)
  ·
    refine ⟨16382676083479445482130209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21843568111305927309506945 16382676083479445482130209)
    ·
      refine ⟨12287007062609584111597657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16382676083479445482130209 12287007062609584111597657)
      ·
        refine ⟨9215255296957188083698243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12287007062609584111597657 9215255296957188083698243)
        ·
          refine ⟨13822882945435782125547365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9215255296957188083698243 13822882945435782125547365)
          ·
            refine ⟨2591790552269209148540131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13822882945435782125547365 2591790552269209148540131)
            ·
              refine ⟨3887685828403813722810197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591790552269209148540131 3887685828403813722810197)
              ·
                refine ⟨22779409150803596032091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3887685828403813722810197 22779409150803596032091)
                ·
                  rfl

theorem cell22_598897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 9].length) (baseStart_598897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598897 prefixEnd_598897 := by exact prefixLift 598897
  have htrace : WordTrace (prefixWord ++ tailWord_598897) baseStart_598897 baseEnd_598897 := by
    simpa [prefixWord, tailWord_598897, baseEnd_598897] using wordTrace_append hprefix tailTrace_598897
  have hstable : (prefixWord ++ tailWord_598897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598897).length < 2 ^ (prefixWord ++ tailWord_598897).sum := by decide
  have hdescent : baseEnd_598897 < baseStart_598897 := by decide
  rcases family_descends (prefixWord ++ tailWord_598897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598974 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_598974 : Nat := 118140960795 + 598974 * 2 ^ 59
def prefixEnd_598974 : Nat := 4983230072969 + 3 ^ 40 * 598974 * 2
def baseEnd_598974 : Nat := 205041041030829830113583

theorem tailTrace_598974 : CollatzResearch.WordTrace tailWord_598974 prefixEnd_598974 205041041030829830113583 := by
  unfold tailWord_598974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730797066503371182507497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14564251021351312973373317 2730797066503371182507497)
  ·
    refine ⟨2048097799877528386880623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2730797066503371182507497 2048097799877528386880623)
    ·
      refine ⟨3072146699816292580320935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048097799877528386880623 3072146699816292580320935)
      ·
        refine ⟨4608220049724438870481403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072146699816292580320935 4608220049724438870481403)
        ·
          refine ⟨6912330074586658305722105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608220049724438870481403 6912330074586658305722105)
          ·
            refine ⟨5184247555939993729291579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6912330074586658305722105 5184247555939993729291579)
            ·
              refine ⟨7776371333909990593937369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184247555939993729291579 7776371333909990593937369)
              ·
                refine ⟨5832278500432492945453027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7776371333909990593937369 5832278500432492945453027)
                ·
                  refine ⟨8748417750648739418179541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5832278500432492945453027 8748417750648739418179541)
                  ·
                    refine ⟨205041041030829830113583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8748417750648739418179541 205041041030829830113583)
                    ·
                      rfl

theorem cell22_598974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_598974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_598974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_598974 prefixEnd_598974 := by exact prefixLift 598974
  have htrace : WordTrace (prefixWord ++ tailWord_598974) baseStart_598974 baseEnd_598974 := by
    simpa [prefixWord, tailWord_598974, baseEnd_598974] using wordTrace_append hprefix tailTrace_598974
  have hstable : (prefixWord ++ tailWord_598974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598974).length < 2 ^ (prefixWord ++ tailWord_598974).sum := by decide
  have hdescent : baseEnd_598974 < baseStart_598974 := by decide
  rcases family_descends (prefixWord ++ tailWord_598974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599010 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_599010 : Nat := 118140960795 + 599010 * 2 ^ 59
def prefixEnd_599010 : Nat := 4983230072969 + 3 ^ 40 * 599010 * 2
def baseEnd_599010 : Nat := 68351121522179245404491

theorem tailTrace_599010 : CollatzResearch.WordTrace tailWord_599010 prefixEnd_599010 68351121522179245404491 := by
  unfold tailWord_599010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461922389974136902092621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14565126373264365072246989 5461922389974136902092621)
  ·
    refine ⟨2048220896240301338284733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5461922389974136902092621 2048220896240301338284733)
    ·
      refine ⟨768082836090113001856775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2048220896240301338284733 768082836090113001856775)
      ·
        refine ⟨1152124254135169502785163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768082836090113001856775 1152124254135169502785163)
        ·
          refine ⟨1728186381202754254177745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152124254135169502785163 1728186381202754254177745)
          ·
            refine ⟨1296139785902065690633309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728186381202754254177745 1296139785902065690633309)
            ·
              refine ⟨486052419713274633987491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1296139785902065690633309 486052419713274633987491)
              ·
                refine ⟨729078629569911950981237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486052419713274633987491 729078629569911950981237)
                ·
                  refine ⟨68351121522179245404491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 729078629569911950981237 68351121522179245404491)
                  ·
                    rfl

theorem cell22_599010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_599010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599010 prefixEnd_599010 := by exact prefixLift 599010
  have htrace : WordTrace (prefixWord ++ tailWord_599010) baseStart_599010 baseEnd_599010 := by
    simpa [prefixWord, tailWord_599010, baseEnd_599010] using wordTrace_append hprefix tailTrace_599010
  have hstable : (prefixWord ++ tailWord_599010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599010).length < 2 ^ (prefixWord ++ tailWord_599010).sum := by decide
  have hdescent : baseEnd_599010 < baseStart_599010 := by decide
  rcases family_descends (prefixWord ++ tailWord_599010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599034 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_599034 : Nat := 118140960795 + 599034 * 2 ^ 59
def prefixEnd_599034 : Nat := 4983230072969 + 3 ^ 40 * 599034 * 2
def baseEnd_599034 : Nat := 205061580257009673613399

theorem tailTrace_599034 : CollatzResearch.WordTrace tailWord_599034 prefixEnd_599034 205061580257009673613399 := by
  unfold tailWord_599034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462141227952399926811039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14565709941206399804829437 5462141227952399926811039)
  ·
    refine ⟨8193211841928599890216559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5462141227952399926811039 8193211841928599890216559)
    ·
      refine ⟨12289817762892899835324839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8193211841928599890216559 12289817762892899835324839)
      ·
        refine ⟨18434726644339349752987259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12289817762892899835324839 18434726644339349752987259)
        ·
          refine ⟨27652089966509024629480889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18434726644339349752987259 27652089966509024629480889)
          ·
            refine ⟨20739067474881768472110667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27652089966509024629480889 20739067474881768472110667)
            ·
              refine ⟨31108601212322652708166001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20739067474881768472110667 31108601212322652708166001)
              ·
                refine ⟨23331450909241989531124501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31108601212322652708166001 23331450909241989531124501)
                ·
                  refine ⟨1093661761370718259271461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23331450909241989531124501 1093661761370718259271461)
                  ·
                    refine ⟨205061580257009673613399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1093661761370718259271461 205061580257009673613399)
                    ·
                      rfl

theorem cell22_599034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_599034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599034 prefixEnd_599034 := by exact prefixLift 599034
  have htrace : WordTrace (prefixWord ++ tailWord_599034) baseStart_599034 baseEnd_599034 := by
    simpa [prefixWord, tailWord_599034, baseEnd_599034] using wordTrace_append hprefix tailTrace_599034
  have hstable : (prefixWord ++ tailWord_599034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599034).length < 2 ^ (prefixWord ++ tailWord_599034).sum := by decide
  have hdescent : baseEnd_599034 < baseStart_599034 := by decide
  rcases family_descends (prefixWord ++ tailWord_599034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599036 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_599036 : Nat := 118140960795 + 599036 * 2 ^ 59
def prefixEnd_599036 : Nat := 4983230072969 + 3 ^ 40 * 599036 * 2
def baseEnd_599036 : Nat := 205062264897882335063393

theorem tailTrace_599036 : CollatzResearch.WordTrace tailWord_599036 prefixEnd_599036 205062264897882335063393 := by
  unfold tailWord_599036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924318928901177024408481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14565758571868236032544641 10924318928901177024408481)
  ·
    refine ⟨8193239196675882768306361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10924318928901177024408481 8193239196675882768306361)
    ·
      refine ⟨6144929397506912076229771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8193239196675882768306361 6144929397506912076229771)
      ·
        refine ⟨9217394096260368114344657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144929397506912076229771 9217394096260368114344657)
        ·
          refine ⟨6913045572195276085758493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9217394096260368114344657 6913045572195276085758493)
          ·
            refine ⟨2592392089573228532159435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6913045572195276085758493 2592392089573228532159435)
            ·
              refine ⟨3888588134359842798239153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592392089573228532159435 3888588134359842798239153)
              ·
                refine ⟨2916441100769882098679365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888588134359842798239153 2916441100769882098679365)
                ·
                  refine ⟨546832706394352893502381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2916441100769882098679365 546832706394352893502381)
                  ·
                    refine ⟨205062264897882335063393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546832706394352893502381 205062264897882335063393)
                    ·
                      rfl

theorem cell22_599036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_599036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599036 prefixEnd_599036 := by exact prefixLift 599036
  have htrace : WordTrace (prefixWord ++ tailWord_599036) baseStart_599036 baseEnd_599036 := by
    simpa [prefixWord, tailWord_599036, baseEnd_599036] using wordTrace_append hprefix tailTrace_599036
  have hstable : (prefixWord ++ tailWord_599036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599036).length < 2 ^ (prefixWord ++ tailWord_599036).sum := by decide
  have hdescent : baseEnd_599036 < baseStart_599036 := by decide
  rcases family_descends (prefixWord ++ tailWord_599036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599051 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 2, 4]
def baseStart_599051 : Nat := 118140960795 + 599051 * 2 ^ 59
def prefixEnd_599051 : Nat := 4983230072969 + 3 ^ 40 * 599051 * 2
def baseEnd_599051 : Nat := 205067399704427295938347

theorem tailTrace_599051 : CollatzResearch.WordTrace tailWord_599051 prefixEnd_599051 205067399704427295938347 := by
  unfold tailWord_599051
  simp only [CollatzResearch.WordTrace]
  refine ⟨21849184952748011610613007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14566123301832007740408671 21849184952748011610613007)
  ·
    refine ⟨32773777429122017415919511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21849184952748011610613007 32773777429122017415919511)
    ·
      refine ⟨49160666143683026123879267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32773777429122017415919511 49160666143683026123879267)
      ·
        refine ⟨73740999215524539185818901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49160666143683026123879267 73740999215524539185818901)
        ·
          refine ⟨3456609338227712774335261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73740999215524539185818901 3456609338227712774335261)
          ·
            refine ⟨1296228501835392290375723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3456609338227712774335261 1296228501835392290375723)
            ·
              refine ⟨1944342752753088435563585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296228501835392290375723 1944342752753088435563585)
              ·
                refine ⟨1458257064564816326672689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944342752753088435563585 1458257064564816326672689)
                ·
                  refine ⟨1093692798423612245004517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1458257064564816326672689 1093692798423612245004517)
                  ·
                    refine ⟨205067399704427295938347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1093692798423612245004517 205067399704427295938347)
                    ·
                      rfl

theorem cell22_599051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_599051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599051 prefixEnd_599051 := by exact prefixLift 599051
  have htrace : WordTrace (prefixWord ++ tailWord_599051) baseStart_599051 baseEnd_599051 := by
    simpa [prefixWord, tailWord_599051, baseEnd_599051] using wordTrace_append hprefix tailTrace_599051
  have hstable : (prefixWord ++ tailWord_599051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599051).length < 2 ^ (prefixWord ++ tailWord_599051).sum := by decide
  have hdescent : baseEnd_599051 < baseStart_599051 := by decide
  rcases family_descends (prefixWord ++ tailWord_599051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599111 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 5]
def baseStart_599111 : Nat := 118140960795 + 599111 * 2 ^ 59
def prefixEnd_599111 : Nat := 4983230072969 + 3 ^ 40 * 599111 * 2
def baseEnd_599111 : Nat := 68362646310202379812721

theorem tailTrace_599111 : CollatzResearch.WordTrace tailWord_599111 prefixEnd_599111 68362646310202379812721 := by
  unfold tailWord_599111
  simp only [CollatzResearch.WordTrace]
  refine ⟨21851373332530641857797187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14567582221687094571864791 21851373332530641857797187)
  ·
    refine ⟨32777059998795962786695781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21851373332530641857797187 32777059998795962786695781)
    ·
      refine ⟨6145698749774243022505459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32777059998795962786695781 6145698749774243022505459)
      ·
        refine ⟨9218548124661364533758189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6145698749774243022505459 9218548124661364533758189)
        ·
          refine ⟨3456955546748011700159321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9218548124661364533758189 3456955546748011700159321)
          ·
            refine ⟨2592716660061008775119491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3456955546748011700159321 2592716660061008775119491)
            ·
              refine ⟨3889074990091513162679237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592716660061008775119491 3889074990091513162679237)
              ·
                refine ⟨729201560642158718002357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3889074990091513162679237 729201560642158718002357)
                ·
                  refine ⟨68362646310202379812721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 729201560642158718002357 68362646310202379812721)
                  ·
                    rfl

theorem cell22_599111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 5].length) (baseStart_599111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599111 prefixEnd_599111 := by exact prefixLift 599111
  have htrace : WordTrace (prefixWord ++ tailWord_599111) baseStart_599111 baseEnd_599111 := by
    simpa [prefixWord, tailWord_599111, baseEnd_599111] using wordTrace_append hprefix tailTrace_599111
  have hstable : (prefixWord ++ tailWord_599111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599111).length < 2 ^ (prefixWord ++ tailWord_599111).sum := by decide
  have hdescent : baseEnd_599111 < baseStart_599111 := by decide
  rcases family_descends (prefixWord ++ tailWord_599111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599141 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_599141 : Nat := 118140960795 + 599141 * 2 ^ 59
def prefixEnd_599141 : Nat := 4983230072969 + 3 ^ 40 * 599141 * 2
def baseEnd_599141 : Nat := 205098208543697061188071

theorem tailTrace_599141 : CollatzResearch.WordTrace tailWord_599141 prefixEnd_599141 205098208543697061188071 := by
  unfold tailWord_599141
  simp only [CollatzResearch.WordTrace]
  refine ⟨21852467522421956981389277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14568311681614637987592851 21852467522421956981389277)
  ·
    refine ⟨8194675320908233868020979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21852467522421956981389277 8194675320908233868020979)
    ·
      refine ⟨12292012981362350802031469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8194675320908233868020979 12292012981362350802031469)
      ·
        refine ⟨4609504868010881550761801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12292012981362350802031469 4609504868010881550761801)
        ·
          refine ⟨3457128651008161163071351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4609504868010881550761801 3457128651008161163071351)
          ·
            refine ⟨5185692976512241744607027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457128651008161163071351 5185692976512241744607027)
            ·
              refine ⟨7778539464768362616910541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185692976512241744607027 7778539464768362616910541)
              ·
                refine ⟨2916952299288135981341453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7778539464768362616910541 2916952299288135981341453)
                ·
                  refine ⟨1093857112233050993003045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2916952299288135981341453 1093857112233050993003045)
                  ·
                    refine ⟨205098208543697061188071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1093857112233050993003045 205098208543697061188071)
                    ·
                      rfl

theorem cell22_599141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_599141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599141 prefixEnd_599141 := by exact prefixLift 599141
  have htrace : WordTrace (prefixWord ++ tailWord_599141) baseStart_599141 baseEnd_599141 := by
    simpa [prefixWord, tailWord_599141, baseEnd_599141] using wordTrace_append hprefix tailTrace_599141
  have hstable : (prefixWord ++ tailWord_599141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599141).length < 2 ^ (prefixWord ++ tailWord_599141).sum := by decide
  have hdescent : baseEnd_599141 < baseStart_599141 := by decide
  rcases family_descends (prefixWord ++ tailWord_599141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599173 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 6]
def baseStart_599173 : Nat := 118140960795 + 599173 * 2 ^ 59
def prefixEnd_599173 : Nat := 4983230072969 + 3 ^ 40 * 599173 * 2
def baseEnd_599173 : Nat := 68369720932553214795991

theorem tailTrace_599173 : CollatzResearch.WordTrace tailWord_599173 prefixEnd_599173 68369720932553214795991 := by
  unfold tailWord_599173
  simp only [CollatzResearch.WordTrace]
  refine ⟨21853634658306026446554173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14569089772204017631036115 21853634658306026446554173)
  ·
    refine ⟨8195112996864759917457815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21853634658306026446554173 8195112996864759917457815)
    ·
      refine ⟨12292669495297139876186723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8195112996864759917457815 12292669495297139876186723)
      ·
        refine ⟨18439004242945709814280085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12292669495297139876186723 18439004242945709814280085)
        ·
          refine ⟨864328323888080147544379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18439004242945709814280085 864328323888080147544379)
          ·
            refine ⟨1296492485832120221316569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864328323888080147544379 1296492485832120221316569)
            ·
              refine ⟨972369364374090165987427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296492485832120221316569 972369364374090165987427)
              ·
                refine ⟨1458554046561135248981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972369364374090165987427 1458554046561135248981141)
                ·
                  refine ⟨68369720932553214795991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1458554046561135248981141 68369720932553214795991)
                  ·
                    rfl

theorem cell22_599173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_599173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599173 prefixEnd_599173 := by exact prefixLift 599173
  have htrace : WordTrace (prefixWord ++ tailWord_599173) baseStart_599173 baseEnd_599173 := by
    simpa [prefixWord, tailWord_599173, baseEnd_599173] using wordTrace_append hprefix tailTrace_599173
  have hstable : (prefixWord ++ tailWord_599173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599173).length < 2 ^ (prefixWord ++ tailWord_599173).sum := by decide
  have hdescent : baseEnd_599173 < baseStart_599173 := by decide
  rcases family_descends (prefixWord ++ tailWord_599173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599201 : List Nat := [1, 2, 3, 3, 1, 1, 3, 8]
def baseStart_599201 : Nat := 118140960795 + 599201 * 2 ^ 59
def prefixEnd_599201 : Nat := 4983230072969 + 3 ^ 40 * 599201 * 2
def baseEnd_599201 : Nat := 22790971974430767187543

theorem tailTrace_599201 : CollatzResearch.WordTrace tailWord_599201 prefixEnd_599201 22790971974430767187543 := by
  unfold tailWord_599201
  simp only [CollatzResearch.WordTrace]
  refine ⟨21854655902204587228573457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14569770601469724819048971 21854655902204587228573457)
  ·
    refine ⟨16390991926653440421430093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21854655902204587228573457 16390991926653440421430093)
    ·
      refine ⟨6146621972495040158036285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16390991926653440421430093 6146621972495040158036285)
      ·
        refine ⟨2304983239685640059263607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6146621972495040158036285 2304983239685640059263607)
        ·
          refine ⟨3457474859528460088895411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304983239685640059263607 3457474859528460088895411)
          ·
            refine ⟨5186212289292690133343117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457474859528460088895411 5186212289292690133343117)
            ·
              refine ⟨1944829608484758800003669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5186212289292690133343117 1944829608484758800003669)
              ·
                refine ⟨22790971974430767187543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1944829608484758800003669 22790971974430767187543)
                ·
                  rfl

theorem cell22_599201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 8].length) (baseStart_599201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599201 prefixEnd_599201 := by exact prefixLift 599201
  have htrace : WordTrace (prefixWord ++ tailWord_599201) baseStart_599201 baseEnd_599201 := by
    simpa [prefixWord, tailWord_599201, baseEnd_599201] using wordTrace_append hprefix tailTrace_599201
  have hstable : (prefixWord ++ tailWord_599201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599201).length < 2 ^ (prefixWord ++ tailWord_599201).sum := by decide
  have hdescent : baseEnd_599201 < baseStart_599201 := by decide
  rcases family_descends (prefixWord ++ tailWord_599201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599207 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 4]
def baseStart_599207 : Nat := 118140960795 + 599207 * 2 ^ 59
def prefixEnd_599207 : Nat := 4983230072969 + 3 ^ 40 * 599207 * 2
def baseEnd_599207 : Nat := 68373600564164963012623

theorem tailTrace_599207 : CollatzResearch.WordTrace tailWord_599207 prefixEnd_599207 68373600564164963012623 := by
  unfold tailWord_599207
  simp only [CollatzResearch.WordTrace]
  refine ⟨21854874740182850253291875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14569916493455233502194583 21854874740182850253291875)
  ·
    refine ⟨32782312110274275379937813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21854874740182850253291875 32782312110274275379937813)
    ·
      refine ⟨1536670880169106658434585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32782312110274275379937813 1536670880169106658434585)
      ·
        refine ⟨1152503160126829993825939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536670880169106658434585 1152503160126829993825939)
        ·
          refine ⟨1728754740190244990738909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152503160126829993825939 1728754740190244990738909)
          ·
            refine ⟨648283027571341871527091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1728754740190244990738909 648283027571341871527091)
            ·
              refine ⟨972424541357012807290637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648283027571341871527091 972424541357012807290637)
              ·
                refine ⟨364659203008879802733989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 972424541357012807290637 364659203008879802733989)
                ·
                  refine ⟨68373600564164963012623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364659203008879802733989 68373600564164963012623)
                  ·
                    rfl

theorem cell22_599207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 4].length) (baseStart_599207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599207 prefixEnd_599207 := by exact prefixLift 599207
  have htrace : WordTrace (prefixWord ++ tailWord_599207) baseStart_599207 baseEnd_599207 := by
    simpa [prefixWord, tailWord_599207, baseEnd_599207] using wordTrace_append hprefix tailTrace_599207
  have hstable : (prefixWord ++ tailWord_599207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599207).length < 2 ^ (prefixWord ++ tailWord_599207).sum := by decide
  have hdescent : baseEnd_599207 < baseStart_599207 := by decide
  rcases family_descends (prefixWord ++ tailWord_599207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599308 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_599308 : Nat := 118140960795 + 599308 * 2 ^ 59
def prefixEnd_599308 : Nat := 4983230072969 + 3 ^ 40 * 599308 * 2
def baseEnd_599308 : Nat := 68385125352188097420853

theorem tailTrace_599308 : CollatzResearch.WordTrace tailWord_599308 prefixEnd_599308 68385125352188097420853 := by
  unfold tailWord_599308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10929279256408472251359289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14572372341877963001812385 10929279256408472251359289)
  ·
    refine ⟨8196959442306354188519467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10929279256408472251359289 8196959442306354188519467)
    ·
      refine ⟨12295439163459531282779201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8196959442306354188519467 12295439163459531282779201)
      ·
        refine ⟨9221579372594648462084401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12295439163459531282779201 9221579372594648462084401)
        ·
          refine ⟨6916184529445986346563301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9221579372594648462084401 6916184529445986346563301)
          ·
            refine ⟨1296784599271122439980619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6916184529445986346563301 1296784599271122439980619)
            ·
              refine ⟨1945176898906683659970929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296784599271122439980619 1945176898906683659970929)
              ·
                refine ⟨1458882674180012744978197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945176898906683659970929 1458882674180012744978197)
                ·
                  refine ⟨68385125352188097420853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1458882674180012744978197 68385125352188097420853)
                  ·
                    rfl

theorem cell22_599308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_599308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599308 prefixEnd_599308 := by exact prefixLift 599308
  have htrace : WordTrace (prefixWord ++ tailWord_599308) baseStart_599308 baseEnd_599308 := by
    simpa [prefixWord, tailWord_599308, baseEnd_599308] using wordTrace_append hprefix tailTrace_599308
  have hstable : (prefixWord ++ tailWord_599308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599308).length < 2 ^ (prefixWord ++ tailWord_599308).sum := by decide
  have hdescent : baseEnd_599308 < baseStart_599308 := by decide
  rcases family_descends (prefixWord ++ tailWord_599308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599323 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 4, 3]
def baseStart_599323 : Nat := 118140960795 + 599323 * 2 ^ 59
def prefixEnd_599323 : Nat := 4983230072969 + 3 ^ 40 * 599323 * 2
def baseEnd_599323 : Nat := 205160510863109253137513

theorem tailTrace_599323 : CollatzResearch.WordTrace tailWord_599323 prefixEnd_599323 205160510863109253137513 := by
  unfold tailWord_599323
  simp only [CollatzResearch.WordTrace]
  refine ⟨21859105607762602064514623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14572737071841734709676415 21859105607762602064514623)
  ·
    refine ⟨32788658411643903096771935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21859105607762602064514623 32788658411643903096771935)
    ·
      refine ⟨49182987617465854645157903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32788658411643903096771935 49182987617465854645157903)
      ·
        refine ⟨73774481426198781967736855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49182987617465854645157903 73774481426198781967736855)
        ·
          refine ⟨110661722139298172951605283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73774481426198781967736855 110661722139298172951605283)
          ·
            refine ⟨165992583208947259427407925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110661722139298172951605283 165992583208947259427407925)
            ·
              refine ⟨15561804675838805571319493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165992583208947259427407925 15561804675838805571319493)
              ·
                refine ⟨2917838376719776044622405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15561804675838805571319493 2917838376719776044622405)
                ·
                  refine ⟨547094695634958008366701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2917838376719776044622405 547094695634958008366701)
                  ·
                    refine ⟨205160510863109253137513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 547094695634958008366701 205160510863109253137513)
                    ·
                      rfl

theorem cell22_599323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 3].length) (baseStart_599323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599323 prefixEnd_599323 := by exact prefixLift 599323
  have htrace : WordTrace (prefixWord ++ tailWord_599323) baseStart_599323 baseEnd_599323 := by
    simpa [prefixWord, tailWord_599323, baseEnd_599323] using wordTrace_append hprefix tailTrace_599323
  have hstable : (prefixWord ++ tailWord_599323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599323).length < 2 ^ (prefixWord ++ tailWord_599323).sum := by decide
  have hdescent : baseEnd_599323 < baseStart_599323 := by decide
  rcases family_descends (prefixWord ++ tailWord_599323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599445 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_599445 : Nat := 118140960795 + 599445 * 2 ^ 59
def prefixEnd_599445 : Nat := 4983230072969 + 3 ^ 40 * 599445 * 2
def baseEnd_599445 : Nat := 205202273956341601587139

theorem tailTrace_599445 : CollatzResearch.WordTrace tailWord_599445 prefixEnd_599445 205202273956341601587139 := by
  unfold tailWord_599445
  simp only [CollatzResearch.WordTrace]
  refine ⟨21863555313320616900455789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14575703542213744600303859 21863555313320616900455789)
  ·
    refine ⟨8198833242495231337670921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21863555313320616900455789 8198833242495231337670921)
    ·
      refine ⟨6149124931871423503253191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8198833242495231337670921 6149124931871423503253191)
      ·
        refine ⟨9223687397807135254879787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6149124931871423503253191 9223687397807135254879787)
        ·
          refine ⟨13835531096710702882319681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9223687397807135254879787 13835531096710702882319681)
          ·
            refine ⟨10376648322533027161739761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13835531096710702882319681 10376648322533027161739761)
            ·
              refine ⟨7782486241899770371304821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10376648322533027161739761 7782486241899770371304821)
              ·
                refine ⟨729608085178103472309827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7782486241899770371304821 729608085178103472309827)
                ·
                  refine ⟨1094412127767155208464741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729608085178103472309827 1094412127767155208464741)
                  ·
                    refine ⟨205202273956341601587139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1094412127767155208464741 205202273956341601587139)
                    ·
                      rfl

theorem cell22_599445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_599445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599445 prefixEnd_599445 := by exact prefixLift 599445
  have htrace : WordTrace (prefixWord ++ tailWord_599445) baseStart_599445 baseEnd_599445 := by
    simpa [prefixWord, tailWord_599445, baseEnd_599445] using wordTrace_append hprefix tailTrace_599445
  have hstable : (prefixWord ++ tailWord_599445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599445).length < 2 ^ (prefixWord ++ tailWord_599445).sum := by decide
  have hdescent : baseEnd_599445 < baseStart_599445 := by decide
  rcases family_descends (prefixWord ++ tailWord_599445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599488 : List Nat := [2, 1, 1, 2, 3, 1, 2, 10]
def baseStart_599488 : Nat := 118140960795 + 599488 * 2 ^ 59
def prefixEnd_599488 : Nat := 4983230072969 + 3 ^ 40 * 599488 * 2
def baseEnd_599488 : Nat := 22801888192789313640223

theorem tailTrace_599488 : CollatzResearch.WordTrace tailWord_599488 prefixEnd_599488 22801888192789313640223 := by
  unfold tailWord_599488
  simp only [CollatzResearch.WordTrace]
  refine ⟨10932561826082417622135559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14576749101443223496180745 10932561826082417622135559)
  ·
    refine ⟨16398842739123626433203339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10932561826082417622135559 16398842739123626433203339)
    ·
      refine ⟨24598264108685439649805009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16398842739123626433203339 24598264108685439649805009)
      ·
        refine ⟨18448698081514079737353757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24598264108685439649805009 18448698081514079737353757)
        ·
          refine ⟨6918261780567779901507659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18448698081514079737353757 6918261780567779901507659)
          ·
            refine ⟨10377392670851669852261489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6918261780567779901507659 10377392670851669852261489)
            ·
              refine ⟨7783044503138752389196117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10377392670851669852261489 7783044503138752389196117)
              ·
                refine ⟨22801888192789313640223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7783044503138752389196117 22801888192789313640223)
                ·
                  rfl

theorem cell22_599488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_599488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599488 prefixEnd_599488 := by exact prefixLift 599488
  have htrace : WordTrace (prefixWord ++ tailWord_599488) baseStart_599488 baseEnd_599488 := by
    simpa [prefixWord, tailWord_599488, baseEnd_599488] using wordTrace_append hprefix tailTrace_599488
  have hstable : (prefixWord ++ tailWord_599488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599488).length < 2 ^ (prefixWord ++ tailWord_599488).sum := by decide
  have hdescent : baseEnd_599488 < baseStart_599488 := by decide
  rcases family_descends (prefixWord ++ tailWord_599488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599492 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_599492 : Nat := 118140960795 + 599492 * 2 ^ 59
def prefixEnd_599492 : Nat := 4983230072969 + 3 ^ 40 * 599492 * 2
def baseEnd_599492 : Nat := 205218363016849145661995

theorem tailTrace_599492 : CollatzResearch.WordTrace tailWord_599492 prefixEnd_599492 205218363016849145661995 := by
  unfold tailWord_599492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10932634772075171963708365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14576846362766895951611153 10932634772075171963708365)
  ·
    refine ⟨4099738039528189486390637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10932634772075171963708365 4099738039528189486390637)
    ·
      refine ⟨1537401764823071057396489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4099738039528189486390637 1537401764823071057396489)
      ·
        refine ⟨1153051323617303293047367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537401764823071057396489 1153051323617303293047367)
        ·
          refine ⟨1729576985425954939571051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153051323617303293047367 1729576985425954939571051)
          ·
            refine ⟨2594365478138932409356577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729576985425954939571051 2594365478138932409356577)
            ·
              refine ⟨1945774108604199307017433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594365478138932409356577 1945774108604199307017433)
              ·
                refine ⟨1459330581453149480263075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945774108604199307017433 1459330581453149480263075)
                ·
                  refine ⟨2188995872179724220394613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459330581453149480263075 2188995872179724220394613)
                  ·
                    refine ⟨205218363016849145661995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2188995872179724220394613 205218363016849145661995)
                    ·
                      rfl

theorem cell22_599492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_599492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599492 prefixEnd_599492 := by exact prefixLift 599492
  have htrace : WordTrace (prefixWord ++ tailWord_599492) baseStart_599492 baseEnd_599492 := by
    simpa [prefixWord, tailWord_599492, baseEnd_599492] using wordTrace_append hprefix tailTrace_599492
  have hstable : (prefixWord ++ tailWord_599492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599492).length < 2 ^ (prefixWord ++ tailWord_599492).sum := by decide
  have hdescent : baseEnd_599492 < baseStart_599492 := by decide
  rcases family_descends (prefixWord ++ tailWord_599492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599537 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_599537 : Nat := 118140960795 + 599537 * 2 ^ 59
def prefixEnd_599537 : Nat := 4983230072969 + 3 ^ 40 * 599537 * 2
def baseEnd_599537 : Nat := 205233767436484028286857

theorem tailTrace_599537 : CollatzResearch.WordTrace tailWord_599537 prefixEnd_599537 205233767436484028286857 := by
  unfold tailWord_599537
  simp only [CollatzResearch.WordTrace]
  refine ⟨21866910828987316612804865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14577940552658211075203243 21866910828987316612804865)
  ·
    refine ⟨16400183121740487459603649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21866910828987316612804865 16400183121740487459603649)
    ·
      refine ⟨12300137341305365594702737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16400183121740487459603649 12300137341305365594702737)
      ·
        refine ⟨9225103005979024196027053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12300137341305365594702737 9225103005979024196027053)
        ·
          refine ⟨3459413627242134073510145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9225103005979024196027053 3459413627242134073510145)
          ·
            refine ⟨2594560220431600555132609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459413627242134073510145 2594560220431600555132609)
            ·
              refine ⟨1945920165323700416349457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594560220431600555132609 1945920165323700416349457)
              ·
                refine ⟨1459440123992775312262093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945920165323700416349457 1459440123992775312262093)
                ·
                  refine ⟨547290046497290742098285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1459440123992775312262093 547290046497290742098285)
                  ·
                    refine ⟨205233767436484028286857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 547290046497290742098285 205233767436484028286857)
                    ·
                      rfl

theorem cell22_599537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_599537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599537 prefixEnd_599537 := by exact prefixLift 599537
  have htrace : WordTrace (prefixWord ++ tailWord_599537) baseStart_599537 baseEnd_599537 := by
    simpa [prefixWord, tailWord_599537, baseEnd_599537] using wordTrace_append hprefix tailTrace_599537
  have hstable : (prefixWord ++ tailWord_599537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599537).length < 2 ^ (prefixWord ++ tailWord_599537).sum := by decide
  have hdescent : baseEnd_599537 < baseStart_599537 := by decide
  rcases family_descends (prefixWord ++ tailWord_599537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599558 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_599558 : Nat := 118140960795 + 599558 * 2 ^ 59
def prefixEnd_599558 : Nat := 4983230072969 + 3 ^ 40 * 599558 * 2
def baseEnd_599558 : Nat := 205240956165646973511793

theorem tailTrace_599558 : CollatzResearch.WordTrace tailWord_599558 prefixEnd_599558 205240956165646973511793 := by
  unfold tailWord_599558
  simp only [CollatzResearch.WordTrace]
  refine ⟨683364898809726162478729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14578451174607491466212885 683364898809726162478729)
  ·
    refine ⟨512523674107294621859047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 683364898809726162478729 512523674107294621859047)
    ·
      refine ⟨768785511160941932788571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512523674107294621859047 768785511160941932788571)
      ·
        refine ⟨1153178266741412899182857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768785511160941932788571 1153178266741412899182857)
        ·
          refine ⟨864883700056059674387143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153178266741412899182857 864883700056059674387143)
          ·
            refine ⟨1297325550084089511580715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864883700056059674387143 1297325550084089511580715)
            ·
              refine ⟨1945988325126134267371073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297325550084089511580715 1945988325126134267371073)
              ·
                refine ⟨1459491243844600700528305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945988325126134267371073 1459491243844600700528305)
                ·
                  refine ⟨1094618432883450525396229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1459491243844600700528305 1094618432883450525396229)
                  ·
                    refine ⟨205240956165646973511793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1094618432883450525396229 205240956165646973511793)
                    ·
                      rfl

theorem cell22_599558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_599558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599558 prefixEnd_599558 := by exact prefixLift 599558
  have htrace : WordTrace (prefixWord ++ tailWord_599558) baseStart_599558 baseEnd_599558 := by
    simpa [prefixWord, tailWord_599558, baseEnd_599558] using wordTrace_append hprefix tailTrace_599558
  have hstable : (prefixWord ++ tailWord_599558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599558).length < 2 ^ (prefixWord ++ tailWord_599558).sum := by decide
  have hdescent : baseEnd_599558 < baseStart_599558 := by decide
  rcases family_descends (prefixWord ++ tailWord_599558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599571 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 1, 3]
def baseStart_599571 : Nat := 118140960795 + 599571 * 2 ^ 59
def prefixEnd_599571 : Nat := 4983230072969 + 3 ^ 40 * 599571 * 2
def baseEnd_599571 : Nat := 205245406331319272936753

theorem tailTrace_599571 : CollatzResearch.WordTrace tailWord_599571 prefixEnd_599571 205245406331319272936753 := by
  unfold tailWord_599571
  simp only [CollatzResearch.WordTrace]
  refine ⟨21868150910864140419542567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14578767273909426946361711 21868150910864140419542567)
  ·
    refine ⟨32802226366296210629313851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21868150910864140419542567 32802226366296210629313851)
    ·
      refine ⟨49203339549444315943970777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32802226366296210629313851 49203339549444315943970777)
      ·
        refine ⟨36902504662083236957978083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49203339549444315943970777 36902504662083236957978083)
        ·
          refine ⟨55353756993124855436967125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36902504662083236957978083 55353756993124855436967125)
          ·
            refine ⟨1297353679526363799303917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55353756993124855436967125 1297353679526363799303917)
            ·
              refine ⟨486507629822386424738969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1297353679526363799303917 486507629822386424738969)
              ·
                refine ⟨364880722366789818554227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486507629822386424738969 364880722366789818554227)
                ·
                  refine ⟨547321083550184727831341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364880722366789818554227 547321083550184727831341)
                  ·
                    refine ⟨205245406331319272936753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 547321083550184727831341 205245406331319272936753)
                    ·
                      rfl

theorem cell22_599571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 3].length) (baseStart_599571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599571 prefixEnd_599571 := by exact prefixLift 599571
  have htrace : WordTrace (prefixWord ++ tailWord_599571) baseStart_599571 baseEnd_599571 := by
    simpa [prefixWord, tailWord_599571, baseEnd_599571] using wordTrace_append hprefix tailTrace_599571
  have hstable : (prefixWord ++ tailWord_599571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599571).length < 2 ^ (prefixWord ++ tailWord_599571).sum := by decide
  have hdescent : baseEnd_599571 < baseStart_599571 := by decide
  rcases family_descends (prefixWord ++ tailWord_599571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599584 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 5]
def baseStart_599584 : Nat := 118140960795 + 599584 * 2 ^ 59
def prefixEnd_599584 : Nat := 4983230072969 + 3 ^ 40 * 599584 * 2
def baseEnd_599584 : Nat := 68416618832330524120571

theorem tailTrace_599584 : CollatzResearch.WordTrace tailWord_599584 prefixEnd_599584 68416618832330524120571 := by
  unfold tailWord_599584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934312529908521819882903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14579083373211362426510537 10934312529908521819882903)
  ·
    refine ⟨16401468794862782729824355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934312529908521819882903 16401468794862782729824355)
    ·
      refine ⟨24602203192294174094736533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16401468794862782729824355 24602203192294174094736533)
      ·
        refine ⟨1153228274638789410690775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24602203192294174094736533 1153228274638789410690775)
        ·
          refine ⟨1729842411958184116036163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153228274638789410690775 1729842411958184116036163)
          ·
            refine ⟨2594763617937276174054245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729842411958184116036163 2594763617937276174054245)
            ·
              refine ⟨486518178363239282635171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2594763617937276174054245 486518178363239282635171)
              ·
                refine ⟨729777267544858923952757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486518178363239282635171 729777267544858923952757)
                ·
                  refine ⟨68416618832330524120571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 729777267544858923952757 68416618832330524120571)
                  ·
                    rfl

theorem cell22_599584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_599584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599584 prefixEnd_599584 := by exact prefixLift 599584
  have htrace : WordTrace (prefixWord ++ tailWord_599584) baseStart_599584 baseEnd_599584 := by
    simpa [prefixWord, tailWord_599584, baseEnd_599584] using wordTrace_append hprefix tailTrace_599584
  have hstable : (prefixWord ++ tailWord_599584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599584).length < 2 ^ (prefixWord ++ tailWord_599584).sum := by decide
  have hdescent : baseEnd_599584 < baseStart_599584 := by decide
  rcases family_descends (prefixWord ++ tailWord_599584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599622 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_599622 : Nat := 118140960795 + 599622 * 2 ^ 59
def prefixEnd_599622 : Nat := 4983230072969 + 3 ^ 40 * 599622 * 2
def baseEnd_599622 : Nat := 205262864673572139911597

theorem tailTrace_599622 : CollatzResearch.WordTrace tailWord_599622 prefixEnd_599622 205262864673572139911597 := by
  unfold tailWord_599622
  simp only [CollatzResearch.WordTrace]
  refine ⟨683437844802480504051535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14580007355786250753099413 683437844802480504051535)
  ·
    refine ⟨1025156767203720756077303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683437844802480504051535 1025156767203720756077303)
    ·
      refine ⟨1537735150805581134115955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025156767203720756077303 1537735150805581134115955)
      ·
        refine ⟨2306602726208371701173933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537735150805581134115955 2306602726208371701173933)
        ·
          refine ⟨864976022328139387940225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2306602726208371701173933 864976022328139387940225)
          ·
            refine ⟨648732016746104540955169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864976022328139387940225 648732016746104540955169)
            ·
              refine ⟨486549012559578405716377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648732016746104540955169 486549012559578405716377)
              ·
                refine ⟨364911759419683804287283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486549012559578405716377 364911759419683804287283)
                ·
                  refine ⟨547367639129525706430925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364911759419683804287283 547367639129525706430925)
                  ·
                    refine ⟨205262864673572139911597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 547367639129525706430925 205262864673572139911597)
                    ·
                      rfl

theorem cell22_599622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_599622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599622 prefixEnd_599622 := by exact prefixLift 599622
  have htrace : WordTrace (prefixWord ++ tailWord_599622) baseStart_599622 baseEnd_599622 := by
    simpa [prefixWord, tailWord_599622, baseEnd_599622] using wordTrace_append hprefix tailTrace_599622
  have hstable : (prefixWord ++ tailWord_599622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599622).length < 2 ^ (prefixWord ++ tailWord_599622).sum := by decide
  have hdescent : baseEnd_599622 < baseStart_599622 := by decide
  rcases family_descends (prefixWord ++ tailWord_599622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599644 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_599644 : Nat := 118140960795 + 599644 * 2 ^ 59
def prefixEnd_599644 : Nat := 4983230072969 + 3 ^ 40 * 599644 * 2
def baseEnd_599644 : Nat := 205270395723171415861529

theorem tailTrace_599644 : CollatzResearch.WordTrace tailWord_599644 prefixEnd_599644 205270395723171415861529 := by
  unfold tailWord_599644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10935406719799836943474993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14580542293066449257966657 10935406719799836943474993)
  ·
    refine ⟨8201555039849877707606245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10935406719799836943474993 8201555039849877707606245)
    ·
      refine ⟨1537791569971852070176171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8201555039849877707606245 1537791569971852070176171)
      ·
        refine ⟨2306687354957778105264257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537791569971852070176171 2306687354957778105264257)
        ·
          refine ⟨1730015516218333578948193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306687354957778105264257 1730015516218333578948193)
          ·
            refine ⟨1297511637163750184211145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1730015516218333578948193 1297511637163750184211145)
            ·
              refine ⟨973133727872812638158359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297511637163750184211145 973133727872812638158359)
              ·
                refine ⟨1459700591809218957237539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973133727872812638158359 1459700591809218957237539)
                ·
                  refine ⟨2189550887713828435856309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459700591809218957237539 2189550887713828435856309)
                  ·
                    refine ⟨205270395723171415861529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2189550887713828435856309 205270395723171415861529)
                    ·
                      rfl

theorem cell22_599644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_599644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599644 prefixEnd_599644 := by exact prefixLift 599644
  have htrace : WordTrace (prefixWord ++ tailWord_599644) baseStart_599644 baseEnd_599644 := by
    simpa [prefixWord, tailWord_599644, baseEnd_599644] using wordTrace_append hprefix tailTrace_599644
  have hstable : (prefixWord ++ tailWord_599644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599644).length < 2 ^ (prefixWord ++ tailWord_599644).sum := by decide
  have hdescent : baseEnd_599644 < baseStart_599644 := by decide
  rcases family_descends (prefixWord ++ tailWord_599644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599794 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_599794 : Nat := 118140960795 + 599794 * 2 ^ 59
def prefixEnd_599794 : Nat := 4983230072969 + 3 ^ 40 * 599794 * 2
def baseEnd_599794 : Nat := 205321743788621024611069

theorem tailTrace_599794 : CollatzResearch.WordTrace tailWord_599794 prefixEnd_599794 205321743788621024611069 := by
  unfold tailWord_599794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469071097264062376227609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14584189592704166336606957 5469071097264062376227609)
  ·
    refine ⟨4101803322948046782170707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5469071097264062376227609 4101803322948046782170707)
    ·
      refine ⟨6152704984422070173256061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101803322948046782170707 6152704984422070173256061)
      ·
        refine ⟨2307264369158276314971023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6152704984422070173256061 2307264369158276314971023)
        ·
          refine ⟨3460896553737414472456535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307264369158276314971023 3460896553737414472456535)
          ·
            refine ⟨5191344830606121708684803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460896553737414472456535 5191344830606121708684803)
            ·
              refine ⟨7787017245909182563027205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191344830606121708684803 7787017245909182563027205)
              ·
                refine ⟨1460065733607971730567601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7787017245909182563027205 1460065733607971730567601)
                ·
                  refine ⟨1095049300205978797925701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460065733607971730567601 1095049300205978797925701)
                  ·
                    refine ⟨205321743788621024611069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095049300205978797925701 205321743788621024611069)
                    ·
                      rfl

theorem cell22_599794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_599794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599794 prefixEnd_599794 := by exact prefixLift 599794
  have htrace : WordTrace (prefixWord ++ tailWord_599794) baseStart_599794 baseEnd_599794 := by
    simpa [prefixWord, tailWord_599794, baseEnd_599794] using wordTrace_append hprefix tailTrace_599794
  have hstable : (prefixWord ++ tailWord_599794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599794).length < 2 ^ (prefixWord ++ tailWord_599794).sum := by decide
  have hdescent : baseEnd_599794 < baseStart_599794 := by decide
  rcases family_descends (prefixWord ++ tailWord_599794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599798 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_599798 : Nat := 118140960795 + 599798 * 2 ^ 59
def prefixEnd_599798 : Nat := 4983230072969 + 3 ^ 40 * 599798 * 2
def baseEnd_599798 : Nat := 68441037690122115837019

theorem tailTrace_599798 : CollatzResearch.WordTrace tailWord_599798 prefixEnd_599798 68441037690122115837019 := by
  unfold tailWord_599798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1367276892565109886753503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14584286854027838792037365 1367276892565109886753503)
  ·
    refine ⟨2050915338847664830130255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1367276892565109886753503 2050915338847664830130255)
    ·
      refine ⟨3076373008271497245195383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2050915338847664830130255 3076373008271497245195383)
      ·
        refine ⟨4614559512407245867793075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076373008271497245195383 4614559512407245867793075)
        ·
          refine ⟨6921839268610868801689613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4614559512407245867793075 6921839268610868801689613)
          ·
            refine ⟨2595689725729075800633605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6921839268610868801689613 2595689725729075800633605)
            ·
              refine ⟨486691823574201712618801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2595689725729075800633605 486691823574201712618801)
              ·
                refine ⟨365018867680651284464101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486691823574201712618801 365018867680651284464101)
                ·
                  refine ⟨68441037690122115837019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365018867680651284464101 68441037690122115837019)
                  ·
                    rfl

theorem cell22_599798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_599798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599798 prefixEnd_599798 := by exact prefixLift 599798
  have htrace : WordTrace (prefixWord ++ tailWord_599798) baseStart_599798 baseEnd_599798 := by
    simpa [prefixWord, tailWord_599798, baseEnd_599798] using wordTrace_append hprefix tailTrace_599798
  have hstable : (prefixWord ++ tailWord_599798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599798).length < 2 ^ (prefixWord ++ tailWord_599798).sum := by decide
  have hdescent : baseEnd_599798 < baseStart_599798 := by decide
  rcases family_descends (prefixWord ++ tailWord_599798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599858 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_599858 : Nat := 118140960795 + 599858 * 2 ^ 59
def prefixEnd_599858 : Nat := 4983230072969 + 3 ^ 40 * 599858 * 2
def baseEnd_599858 : Nat := 205343652296546191010873

theorem tailTrace_599858 : CollatzResearch.WordTrace tailWord_599858 prefixEnd_599858 205343652296546191010873 := by
  unfold tailWord_599858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469654665206097108810057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14585745773882925623493485 5469654665206097108810057)
  ·
    refine ⟨4102240998904572831607543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5469654665206097108810057 4102240998904572831607543)
    ·
      refine ⟨6153361498356859247411315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4102240998904572831607543 6153361498356859247411315)
      ·
        refine ⟨9230042247535288871116973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6153361498356859247411315 9230042247535288871116973)
        ·
          refine ⟨3461265842825733326668865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9230042247535288871116973 3461265842825733326668865)
          ·
            refine ⟨2595949382119299995001649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3461265842825733326668865 2595949382119299995001649)
            ·
              refine ⟨1946962036589474996251237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2595949382119299995001649 1946962036589474996251237)
              ·
                refine ⟨365055381860526561797107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1946962036589474996251237 365055381860526561797107)
                ·
                  refine ⟨547583072790789842695661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365055381860526561797107 547583072790789842695661)
                  ·
                    refine ⟨205343652296546191010873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 547583072790789842695661 205343652296546191010873)
                    ·
                      rfl

theorem cell22_599858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_599858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599858 prefixEnd_599858 := by exact prefixLift 599858
  have htrace : WordTrace (prefixWord ++ tailWord_599858) baseStart_599858 baseEnd_599858 := by
    simpa [prefixWord, tailWord_599858, baseEnd_599858] using wordTrace_append hprefix tailTrace_599858
  have hstable : (prefixWord ++ tailWord_599858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599858).length < 2 ^ (prefixWord ++ tailWord_599858).sum := by decide
  have hdescent : baseEnd_599858 < baseStart_599858 := by decide
  rcases family_descends (prefixWord ++ tailWord_599858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599916 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 6]
def baseStart_599916 : Nat := 118140960795 + 599916 * 2 ^ 59
def prefixEnd_599916 : Nat := 4983230072969 + 3 ^ 40 * 599916 * 2
def baseEnd_599916 : Nat := 68454502293951124353565

theorem tailTrace_599916 : CollatzResearch.WordTrace tailWord_599916 prefixEnd_599916 68454502293951124353565 := by
  unfold tailWord_599916
  simp only [CollatzResearch.WordTrace]
  refine ⟨10940367047307132170425801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14587156063076176227234401 10940367047307132170425801)
  ·
    refine ⟨8205275285480349127819351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10940367047307132170425801 8205275285480349127819351)
    ·
      refine ⟨12307912928220523691729027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8205275285480349127819351 12307912928220523691729027)
      ·
        refine ⟨18461869392330785537593541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12307912928220523691729027 18461869392330785537593541)
        ·
          refine ⟨3461600511062022288298789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18461869392330785537593541 3461600511062022288298789)
          ·
            refine ⟨649050095824129179056023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3461600511062022288298789 649050095824129179056023)
            ·
              refine ⟨973575143736193768584035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649050095824129179056023 973575143736193768584035)
              ·
                refine ⟨1460362715604290652876053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973575143736193768584035 1460362715604290652876053)
                ·
                  refine ⟨68454502293951124353565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1460362715604290652876053 68454502293951124353565)
                  ·
                    rfl

theorem cell22_599916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_599916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599916 prefixEnd_599916 := by exact prefixLift 599916
  have htrace : WordTrace (prefixWord ++ tailWord_599916) baseStart_599916 baseEnd_599916 := by
    simpa [prefixWord, tailWord_599916, baseEnd_599916] using wordTrace_append hprefix tailTrace_599916
  have hstable : (prefixWord ++ tailWord_599916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599916).length < 2 ^ (prefixWord ++ tailWord_599916).sum := by decide
  have hdescent : baseEnd_599916 < baseStart_599916 := by decide
  rcases family_descends (prefixWord ++ tailWord_599916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599929 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_599929 : Nat := 118140960795 + 599929 * 2 ^ 59
def prefixEnd_599929 : Nat := 4983230072969 + 3 ^ 40 * 599929 * 2
def baseEnd_599929 : Nat := 205367957047525672485655

theorem tailTrace_599929 : CollatzResearch.WordTrace tailWord_599929 prefixEnd_599929 205367957047525672485655 := by
  unfold tailWord_599929
  simp only [CollatzResearch.WordTrace]
  refine ⟨21881208243567167561074841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14587472162378111707383227 21881208243567167561074841)
  ·
    refine ⟨16410906182675375670806131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21881208243567167561074841 16410906182675375670806131)
    ·
      refine ⟨24616359274013063506209197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16410906182675375670806131 24616359274013063506209197)
      ·
        refine ⟨9231134727754898814828449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24616359274013063506209197 9231134727754898814828449)
        ·
          refine ⟨6923351045816174111121337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9231134727754898814828449 6923351045816174111121337)
          ·
            refine ⟨5192513284362130583341003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6923351045816174111121337 5192513284362130583341003)
            ·
              refine ⟨7788769926543195875011505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192513284362130583341003 7788769926543195875011505)
              ·
                refine ⟨5841577444907396906258629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7788769926543195875011505 5841577444907396906258629)
                ·
                  refine ⟨1095295770920136919923493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5841577444907396906258629 1095295770920136919923493)
                  ·
                    refine ⟨205367957047525672485655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095295770920136919923493 205367957047525672485655)
                    ·
                      rfl

theorem cell22_599929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_599929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599929 prefixEnd_599929 := by exact prefixLift 599929
  have htrace : WordTrace (prefixWord ++ tailWord_599929) baseStart_599929 baseEnd_599929 := by
    simpa [prefixWord, tailWord_599929, baseEnd_599929] using wordTrace_append hprefix tailTrace_599929
  have hstable : (prefixWord ++ tailWord_599929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599929).length < 2 ^ (prefixWord ++ tailWord_599929).sum := by decide
  have hdescent : baseEnd_599929 < baseStart_599929 := by decide
  rcases family_descends (prefixWord ++ tailWord_599929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599967 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 4]
def baseStart_599967 : Nat := 118140960795 + 599967 * 2 ^ 59
def prefixEnd_599967 : Nat := 4983230072969 + 3 ^ 40 * 599967 * 2
def baseEnd_599967 : Nat := 68460321741368746678513

theorem tailTrace_599967 : CollatzResearch.WordTrace tailWord_599967 prefixEnd_599967 68460321741368746678513 := by
  unfold tailWord_599967
  simp only [CollatzResearch.WordTrace]
  refine ⟨21882594217429500050958155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14588396144953000033972103 21882594217429500050958155)
  ·
    refine ⟨32823891326144250076437233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21882594217429500050958155 32823891326144250076437233)
    ·
      refine ⟨24617918494608187557327925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32823891326144250076437233 24617918494608187557327925)
      ·
        refine ⟨2307929858869517583499493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24617918494608187557327925 2307929858869517583499493)
        ·
          refine ⟨432736848538034546906155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2307929858869517583499493 432736848538034546906155)
          ·
            refine ⟨649105272807051820359233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432736848538034546906155 649105272807051820359233)
            ·
              refine ⟨486828954605288865269425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649105272807051820359233 486828954605288865269425)
              ·
                refine ⟨365121715953966648952069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486828954605288865269425 365121715953966648952069)
                ·
                  refine ⟨68460321741368746678513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365121715953966648952069 68460321741368746678513)
                  ·
                    rfl

theorem cell22_599967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 4].length) (baseStart_599967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599967 prefixEnd_599967 := by exact prefixLift 599967
  have htrace : WordTrace (prefixWord ++ tailWord_599967) baseStart_599967 baseEnd_599967 := by
    simpa [prefixWord, tailWord_599967, baseEnd_599967] using wordTrace_append hprefix tailTrace_599967
  have hstable : (prefixWord ++ tailWord_599967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599967).length < 2 ^ (prefixWord ++ tailWord_599967).sum := by decide
  have hdescent : baseEnd_599967 < baseStart_599967 := by decide
  rcases family_descends (prefixWord ++ tailWord_599967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599982 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_599982 : Nat := 118140960795 + 599982 * 2 ^ 59
def prefixEnd_599982 : Nat := 4983230072969 + 3 ^ 40 * 599982 * 2
def baseEnd_599982 : Nat := 205386100030651200910493

theorem tailTrace_599982 : CollatzResearch.WordTrace tailWord_599982 prefixEnd_599982 205386100030651200910493 := by
  unfold tailWord_599982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735392664046894701594275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14588760874916771741836133 2735392664046894701594275)
  ·
    refine ⟨4103088996070342052391413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2735392664046894701594275 4103088996070342052391413)
    ·
      refine ⟨384664593381594567411695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4103088996070342052391413 384664593381594567411695)
      ·
        refine ⟨576996890072391851117543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384664593381594567411695 576996890072391851117543)
        ·
          refine ⟨865495335108587776676315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576996890072391851117543 865495335108587776676315)
          ·
            refine ⟨1298243002662881665014473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865495335108587776676315 1298243002662881665014473)
            ·
              refine ⟨973682251997161248760855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298243002662881665014473 973682251997161248760855)
              ·
                refine ⟨1460523377995741873141283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973682251997161248760855 1460523377995741873141283)
                ·
                  refine ⟨2190785066993612809711925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460523377995741873141283 2190785066993612809711925)
                  ·
                    refine ⟨205386100030651200910493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2190785066993612809711925 205386100030651200910493)
                    ·
                      rfl

theorem cell22_599982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_599982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_599982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_599982 prefixEnd_599982 := by exact prefixLift 599982
  have htrace : WordTrace (prefixWord ++ tailWord_599982) baseStart_599982 baseEnd_599982 := by
    simpa [prefixWord, tailWord_599982, baseEnd_599982] using wordTrace_append hprefix tailTrace_599982
  have hstable : (prefixWord ++ tailWord_599982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599982).length < 2 ^ (prefixWord ++ tailWord_599982).sum := by decide
  have hdescent : baseEnd_599982 < baseStart_599982 := by decide
  rcases family_descends (prefixWord ++ tailWord_599982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600021 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_600021 : Nat := 118140960795 + 600021 * 2 ^ 59
def prefixEnd_600021 : Nat := 4983230072969 + 3 ^ 40 * 600021 * 2
def baseEnd_600021 : Nat := 205399450527668099185373

theorem tailTrace_600021 : CollatzResearch.WordTrace tailWord_600021 prefixEnd_600021 205399450527668099185373 := by
  unfold tailWord_600021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21884563759233867273423917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14589709172822578182282611 21884563759233867273423917)
  ·
    refine ⟨8206711409712700227533969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21884563759233867273423917 8206711409712700227533969)
    ·
      refine ⟨6155033557284525170650477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8206711409712700227533969 6155033557284525170650477)
      ·
        refine ⟨2308137583981696938993929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6155033557284525170650477 2308137583981696938993929)
        ·
          refine ⟨1731103187986272704245447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2308137583981696938993929 1731103187986272704245447)
          ·
            refine ⟨2596654781979409056368171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731103187986272704245447 2596654781979409056368171)
            ·
              refine ⟨3894982172969113584552257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596654781979409056368171 3894982172969113584552257)
              ·
                refine ⟨2921236629726835188414193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894982172969113584552257 2921236629726835188414193)
                ·
                  refine ⟨2190927472295126391310645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921236629726835188414193 2190927472295126391310645)
                  ·
                    refine ⟨205399450527668099185373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2190927472295126391310645 205399450527668099185373)
                    ·
                      rfl

theorem cell22_600021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_600021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600021 prefixEnd_600021 := by exact prefixLift 600021
  have htrace : WordTrace (prefixWord ++ tailWord_600021) baseStart_600021 baseEnd_600021 := by
    simpa [prefixWord, tailWord_600021, baseEnd_600021] using wordTrace_append hprefix tailTrace_600021
  have hstable : (prefixWord ++ tailWord_600021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600021).length < 2 ^ (prefixWord ++ tailWord_600021).sum := by decide
  have hdescent : baseEnd_600021 < baseStart_600021 := by decide
  rcases family_descends (prefixWord ++ tailWord_600021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600085 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 6]
def baseStart_600085 : Nat := 118140960795 + 600085 * 2 ^ 59
def prefixEnd_600085 : Nat := 4983230072969 + 3 ^ 40 * 600085 * 2
def baseEnd_600085 : Nat := 68473786345197755195059

theorem tailTrace_600085 : CollatzResearch.WordTrace tailWord_600085 prefixEnd_600085 68473786345197755195059 := by
  unfold tailWord_600085
  simp only [CollatzResearch.WordTrace]
  refine ⟨21886898031002006203753709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14591265354001337469169139 21886898031002006203753709)
  ·
    refine ⟨8207586761625752326407641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21886898031002006203753709 8207586761625752326407641)
    ·
      refine ⟨6155690071219314244805731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8207586761625752326407641 6155690071219314244805731)
      ·
        refine ⟨9233535106828971367208597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6155690071219314244805731 9233535106828971367208597)
        ·
          refine ⟨432821958132608032837903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9233535106828971367208597 432821958132608032837903)
          ·
            refine ⟨649232937198912049256855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432821958132608032837903 649232937198912049256855)
            ·
              refine ⟨973849405798368073885283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649232937198912049256855 973849405798368073885283)
              ·
                refine ⟨1460774108697552110827925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973849405798368073885283 1460774108697552110827925)
                ·
                  refine ⟨68473786345197755195059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1460774108697552110827925 68473786345197755195059)
                  ·
                    rfl

theorem cell22_600085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_600085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600085 prefixEnd_600085 := by exact prefixLift 600085
  have htrace : WordTrace (prefixWord ++ tailWord_600085) baseStart_600085 baseEnd_600085 := by
    simpa [prefixWord, tailWord_600085, baseEnd_600085] using wordTrace_append hprefix tailTrace_600085
  have hstable : (prefixWord ++ tailWord_600085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600085).length < 2 ^ (prefixWord ++ tailWord_600085).sum := by decide
  have hdescent : baseEnd_600085 < baseStart_600085 := by decide
  rcases family_descends (prefixWord ++ tailWord_600085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600104 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 1, 4]
def baseStart_600104 : Nat := 118140960795 + 600104 * 2 ^ 59
def prefixEnd_600104 : Nat := 4983230072969 + 3 ^ 40 * 600104 * 2
def baseEnd_600104 : Nat := 205427863123883549360119

theorem tailTrace_600104 : CollatzResearch.WordTrace tailWord_600104 prefixEnd_600104 205427863123883549360119 := by
  unfold tailWord_600104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10943795508966586224347683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14591727345288781632463577 10943795508966586224347683)
  ·
    refine ⟨16415693263449879336521525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10943795508966586224347683 16415693263449879336521525)
    ·
      refine ⟨1538971243448426187798893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16415693263449879336521525 1538971243448426187798893)
      ·
        refine ⟨577114216293159820424585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1538971243448426187798893 577114216293159820424585)
        ·
          refine ⟨432835662219869865318439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577114216293159820424585 432835662219869865318439)
          ·
            refine ⟨649253493329804797977659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432835662219869865318439 649253493329804797977659)
            ·
              refine ⟨973880239994707196966489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649253493329804797977659 973880239994707196966489)
              ·
                refine ⟨730410179996030397724867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973880239994707196966489 730410179996030397724867)
                ·
                  refine ⟨1095615269994045596587301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730410179996030397724867 1095615269994045596587301)
                  ·
                    refine ⟨205427863123883549360119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095615269994045596587301 205427863123883549360119)
                    ·
                      rfl

theorem cell22_600104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_600104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600104 prefixEnd_600104 := by exact prefixLift 600104
  have htrace : WordTrace (prefixWord ++ tailWord_600104) baseStart_600104 baseEnd_600104 := by
    simpa [prefixWord, tailWord_600104, baseEnd_600104] using wordTrace_append hprefix tailTrace_600104
  have hstable : (prefixWord ++ tailWord_600104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600104).length < 2 ^ (prefixWord ++ tailWord_600104).sum := by decide
  have hdescent : baseEnd_600104 < baseStart_600104 := by decide
  rcases family_descends (prefixWord ++ tailWord_600104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600162 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_600162 : Nat := 118140960795 + 600162 * 2 ^ 59
def prefixEnd_600162 : Nat := 4983230072969 + 3 ^ 40 * 600162 * 2
def baseEnd_600162 : Nat := 205447717709190731409941

theorem tailTrace_600162 : CollatzResearch.WordTrace tailWord_600162 prefixEnd_600162 205447717709190731409941 := by
  unfold tailWord_600162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472426612930762088576685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14593137634482032236204493 5472426612930762088576685)
  ·
    refine ⟨2052159979849035783216257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5472426612930762088576685 2052159979849035783216257)
    ·
      refine ⟨1539119984886776837412193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2052159979849035783216257 1539119984886776837412193)
      ·
        refine ⟨1154339988665082628059145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539119984886776837412193 1154339988665082628059145)
        ·
          refine ⟨865754991498811971044359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154339988665082628059145 865754991498811971044359)
          ·
            refine ⟨1298632487248217956566539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865754991498811971044359 1298632487248217956566539)
            ·
              refine ⟨1947948730872326934849809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298632487248217956566539 1947948730872326934849809)
              ·
                refine ⟨1460961548154245201137357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947948730872326934849809 1460961548154245201137357)
                ·
                  refine ⟨547860580557841950426509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1460961548154245201137357 547860580557841950426509)
                  ·
                    refine ⟨205447717709190731409941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 547860580557841950426509 205447717709190731409941)
                    ·
                      rfl

theorem cell22_600162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_600162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600162 prefixEnd_600162 := by exact prefixLift 600162
  have htrace : WordTrace (prefixWord ++ tailWord_600162) baseStart_600162 baseEnd_600162 := by
    simpa [prefixWord, tailWord_600162, baseEnd_600162] using wordTrace_append hprefix tailTrace_600162
  have hstable : (prefixWord ++ tailWord_600162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600162).length < 2 ^ (prefixWord ++ tailWord_600162).sum := by decide
  have hdescent : baseEnd_600162 < baseStart_600162 := by decide
  rcases family_descends (prefixWord ++ tailWord_600162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600237 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 4]
def baseStart_600237 : Nat := 118140960795 + 600237 * 2 ^ 59
def prefixEnd_600237 : Nat := 4983230072969 + 3 ^ 40 * 600237 * 2
def baseEnd_600237 : Nat := 68491130580638511928237

theorem tailTrace_600237 : CollatzResearch.WordTrace tailWord_600237 prefixEnd_600237 68491130580638511928237 := by
  unfold tailWord_600237
  simp only [CollatzResearch.WordTrace]
  refine ⟨21892441926451336163286965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14594961284300890775524643 21892441926451336163286965)
  ·
    refine ⟨2052416430604812765308153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21892441926451336163286965 2052416430604812765308153)
    ·
      refine ⟨1539312322953609573981115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2052416430604812765308153 1539312322953609573981115)
      ·
        refine ⟨2308968484430414360971673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539312322953609573981115 2308968484430414360971673)
        ·
          refine ⟨1731726363322810770728755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2308968484430414360971673 1731726363322810770728755)
          ·
            refine ⟨2597589544984216156093133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731726363322810770728755 2597589544984216156093133)
            ·
              refine ⟨974096079369081058534925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2597589544984216156093133 974096079369081058534925)
              ·
                refine ⟨365286029763405396950597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 974096079369081058534925 365286029763405396950597)
                ·
                  refine ⟨68491130580638511928237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365286029763405396950597 68491130580638511928237)
                  ·
                    rfl

theorem cell22_600237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_600237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600237 prefixEnd_600237 := by exact prefixLift 600237
  have htrace : WordTrace (prefixWord ++ tailWord_600237) baseStart_600237 baseEnd_600237 := by
    simpa [prefixWord, tailWord_600237, baseEnd_600237] using wordTrace_append hprefix tailTrace_600237
  have hstable : (prefixWord ++ tailWord_600237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600237).length < 2 ^ (prefixWord ++ tailWord_600237).sum := by decide
  have hdescent : baseEnd_600237 < baseStart_600237 := by decide
  rcases family_descends (prefixWord ++ tailWord_600237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600254 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_600254 : Nat := 118140960795 + 600254 * 2 ^ 59
def prefixEnd_600254 : Nat := 4983230072969 + 3 ^ 40 * 600254 * 2
def baseEnd_600254 : Nat := 68493070396444386036553

theorem tailTrace_600254 : CollatzResearch.WordTrace tailWord_600254 prefixEnd_600254 68493070396444386036553 := by
  unfold tailWord_600254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736632745923718508331977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14595374644926498711103877 2736632745923718508331977)
  ·
    refine ⟨2052474559442788881248983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2736632745923718508331977 2052474559442788881248983)
    ·
      refine ⟨3078711839164183321873475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052474559442788881248983 3078711839164183321873475)
      ·
        refine ⟨4618067758746274982810213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078711839164183321873475 4618067758746274982810213)
        ·
          refine ⟨865887704764926559276915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4618067758746274982810213 865887704764926559276915)
          ·
            refine ⟨1298831557147389838915373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865887704764926559276915 1298831557147389838915373)
            ·
              refine ⟨487061833930271189593265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1298831557147389838915373 487061833930271189593265)
              ·
                refine ⟨365296375447703392194949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487061833930271189593265 365296375447703392194949)
                ·
                  refine ⟨68493070396444386036553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365296375447703392194949 68493070396444386036553)
                  ·
                    rfl

theorem cell22_600254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_600254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600254 prefixEnd_600254 := by exact prefixLift 600254
  have htrace : WordTrace (prefixWord ++ tailWord_600254) baseStart_600254 baseEnd_600254 := by
    simpa [prefixWord, tailWord_600254, baseEnd_600254] using wordTrace_append hprefix tailTrace_600254
  have hstable : (prefixWord ++ tailWord_600254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600254).length < 2 ^ (prefixWord ++ tailWord_600254).sum := by decide
  have hdescent : baseEnd_600254 < baseStart_600254 := by decide
  rcases family_descends (prefixWord ++ tailWord_600254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600284 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_600284 : Nat := 118140960795 + 600284 * 2 ^ 59
def prefixEnd_600284 : Nat := 4983230072969 + 3 ^ 40 * 600284 * 2
def baseEnd_600284 : Nat := 205489480802423079859567

theorem tailTrace_600284 : CollatzResearch.WordTrace tailWord_600284 prefixEnd_600284 205489480802423079859567 := by
  unfold tailWord_600284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10947078078640531595123953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14596104104854042126831937 10947078078640531595123953)
  ·
    refine ⟨8210308558980398696342965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10947078078640531595123953 8210308558980398696342965)
    ·
      refine ⟨769716427404412377782153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8210308558980398696342965 769716427404412377782153)
      ·
        refine ⟨577287320553309283336615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769716427404412377782153 577287320553309283336615)
        ·
          refine ⟨865930980829963925004923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577287320553309283336615 865930980829963925004923)
          ·
            refine ⟨1298896471244945887507385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865930980829963925004923 1298896471244945887507385)
            ·
              refine ⟨974172353433709415630539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298896471244945887507385 974172353433709415630539)
              ·
                refine ⟨1461258530150564123445809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974172353433709415630539 1461258530150564123445809)
                ·
                  refine ⟨1095943897612923092584357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461258530150564123445809 1095943897612923092584357)
                  ·
                    refine ⟨205489480802423079859567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095943897612923092584357 205489480802423079859567)
                    ·
                      rfl

theorem cell22_600284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_600284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600284 prefixEnd_600284 := by exact prefixLift 600284
  have htrace : WordTrace (prefixWord ++ tailWord_600284) baseStart_600284 baseEnd_600284 := by
    simpa [prefixWord, tailWord_600284, baseEnd_600284] using wordTrace_append hprefix tailTrace_600284
  have hstable : (prefixWord ++ tailWord_600284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600284).length < 2 ^ (prefixWord ++ tailWord_600284).sum := by decide
  have hdescent : baseEnd_600284 < baseStart_600284 := by decide
  rcases family_descends (prefixWord ++ tailWord_600284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600310 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_600310 : Nat := 118140960795 + 600310 * 2 ^ 59
def prefixEnd_600310 : Nat := 4983230072969 + 3 ^ 40 * 600310 * 2
def baseEnd_600310 : Nat := 68499460377922559569829

theorem tailTrace_600310 : CollatzResearch.WordTrace tailWord_600310 prefixEnd_600310 68499460377922559569829 := by
  unfold tailWord_600310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368444028449179351918399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14596736303457913087129589 1368444028449179351918399)
  ·
    refine ⟨2052666042673769027877599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1368444028449179351918399 2052666042673769027877599)
    ·
      refine ⟨3078999064010653541816399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052666042673769027877599 3078999064010653541816399)
      ·
        refine ⟨4618498596015980312724599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078999064010653541816399 4618498596015980312724599)
        ·
          refine ⟨6927747894023970469086899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618498596015980312724599 6927747894023970469086899)
          ·
            refine ⟨10391621841035955703630349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927747894023970469086899 10391621841035955703630349)
            ·
              refine ⟨3896858190388483388861381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10391621841035955703630349 3896858190388483388861381)
              ·
                refine ⟨730660910697840635411509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3896858190388483388861381 730660910697840635411509)
                ·
                  refine ⟨68499460377922559569829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 730660910697840635411509 68499460377922559569829)
                  ·
                    rfl

theorem cell22_600310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_600310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600310 prefixEnd_600310 := by exact prefixLift 600310
  have htrace : WordTrace (prefixWord ++ tailWord_600310) baseStart_600310 baseEnd_600310 := by
    simpa [prefixWord, tailWord_600310, baseEnd_600310] using wordTrace_append hprefix tailTrace_600310
  have hstable : (prefixWord ++ tailWord_600310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600310).length < 2 ^ (prefixWord ++ tailWord_600310).sum := by decide
  have hdescent : baseEnd_600310 < baseStart_600310 := by decide
  rcases family_descends (prefixWord ++ tailWord_600310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600314 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_600314 : Nat := 118140960795 + 600314 * 2 ^ 59
def prefixEnd_600314 : Nat := 4983230072969 + 3 ^ 40 * 600314 * 2
def baseEnd_600314 : Nat := 205499750415513001609475

theorem tailTrace_600314 : CollatzResearch.WordTrace tailWord_600314 prefixEnd_600314 205499750415513001609475 := by
  unfold tailWord_600314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473812586793094578459999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14596833564781585542559997 5473812586793094578459999)
  ·
    refine ⟨8210718880189641867689999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5473812586793094578459999 8210718880189641867689999)
    ·
      refine ⟨12316078320284462801534999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8210718880189641867689999 12316078320284462801534999)
      ·
        refine ⟨18474117480426694202302499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12316078320284462801534999 18474117480426694202302499)
        ·
          refine ⟨27711176220640041303453749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18474117480426694202302499 27711176220640041303453749)
          ·
            refine ⟨2597922770685003872198789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27711176220640041303453749 2597922770685003872198789)
            ·
              refine ⟨487110519503438226037273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2597922770685003872198789 487110519503438226037273)
              ·
                refine ⟨365332889627578669527955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487110519503438226037273 365332889627578669527955)
                ·
                  refine ⟨547999334441368004291933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365332889627578669527955 547999334441368004291933)
                  ·
                    refine ⟨205499750415513001609475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 547999334441368004291933 205499750415513001609475)
                    ·
                      rfl

theorem cell22_600314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_600314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600314 prefixEnd_600314 := by exact prefixLift 600314
  have htrace : WordTrace (prefixWord ++ tailWord_600314) baseStart_600314 baseEnd_600314 := by
    simpa [prefixWord, tailWord_600314, baseEnd_600314] using wordTrace_append hprefix tailTrace_600314
  have hstable : (prefixWord ++ tailWord_600314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600314).length < 2 ^ (prefixWord ++ tailWord_600314).sum := by decide
  have hdescent : baseEnd_600314 < baseStart_600314 := by decide
  rcases family_descends (prefixWord ++ tailWord_600314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600323 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 5, 4]
def baseStart_600323 : Nat := 118140960795 + 600323 * 2 ^ 59
def prefixEnd_600323 : Nat := 4983230072969 + 3 ^ 40 * 600323 * 2
def baseEnd_600323 : Nat := 205502831299439978134447

theorem tailTrace_600323 : CollatzResearch.WordTrace tailWord_600323 prefixEnd_600323 205502831299439978134447 := by
  unfold tailWord_600323
  simp only [CollatzResearch.WordTrace]
  refine ⟨21895578604139772850917623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14597052402759848567278415 21895578604139772850917623)
  ·
    refine ⟨32843367906209659276376435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21895578604139772850917623 32843367906209659276376435)
    ·
      refine ⟨49265051859314488914564653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32843367906209659276376435 49265051859314488914564653)
      ·
        refine ⟨18474394447242933342961745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49265051859314488914564653 18474394447242933342961745)
        ·
          refine ⟨13855795835432200007221309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18474394447242933342961745 13855795835432200007221309)
          ·
            refine ⟨5195923438287075002707991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13855795835432200007221309 5195923438287075002707991)
            ·
              refine ⟨7793885157430612504061987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195923438287075002707991 7793885157430612504061987)
              ·
                refine ⟨11690827736145918756092981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7793885157430612504061987 11690827736145918756092981)
                ·
                  refine ⟨1096015100263679883383717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11690827736145918756092981 1096015100263679883383717)
                  ·
                    refine ⟨205502831299439978134447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096015100263679883383717 205502831299439978134447)
                    ·
                      rfl

theorem cell22_600323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_600323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600323 prefixEnd_600323 := by exact prefixLift 600323
  have htrace : WordTrace (prefixWord ++ tailWord_600323) baseStart_600323 baseEnd_600323 := by
    simpa [prefixWord, tailWord_600323, baseEnd_600323] using wordTrace_append hprefix tailTrace_600323
  have hstable : (prefixWord ++ tailWord_600323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600323).length < 2 ^ (prefixWord ++ tailWord_600323).sum := by decide
  have hdescent : baseEnd_600323 < baseStart_600323 := by decide
  rcases family_descends (prefixWord ++ tailWord_600323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600357 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_600357 : Nat := 118140960795 + 600357 * 2 ^ 59
def prefixEnd_600357 : Nat := 4983230072969 + 3 ^ 40 * 600357 * 2
def baseEnd_600357 : Nat := 205514470194275222784343

theorem tailTrace_600357 : CollatzResearch.WordTrace tailWord_600357 prefixEnd_600357 205514470194275222784343 := by
  unfold tailWord_600357
  simp only [CollatzResearch.WordTrace]
  refine ⟨21896818686016596657655325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14597879124011064438436883 21896818686016596657655325)
  ·
    refine ⟨8211307007256223746620747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21896818686016596657655325 8211307007256223746620747)
    ·
      refine ⟨12316960510884335619931121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8211307007256223746620747 12316960510884335619931121)
      ·
        refine ⟨9237720383163251714948341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12316960510884335619931121 9237720383163251714948341)
        ·
          refine ⟨866036285921554848276407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9237720383163251714948341 866036285921554848276407)
          ·
            refine ⟨1299054428882332272414611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866036285921554848276407 1299054428882332272414611)
            ·
              refine ⟨1948581643323498408621917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299054428882332272414611 1948581643323498408621917)
              ·
                refine ⟨730718116246311903233219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1948581643323498408621917 730718116246311903233219)
                ·
                  refine ⟨1096077174369467854849829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730718116246311903233219 1096077174369467854849829)
                  ·
                    refine ⟨205514470194275222784343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096077174369467854849829 205514470194275222784343)
                    ·
                      rfl

theorem cell22_600357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_600357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600357 prefixEnd_600357 := by exact prefixLift 600357
  have htrace : WordTrace (prefixWord ++ tailWord_600357) baseStart_600357 baseEnd_600357 := by
    simpa [prefixWord, tailWord_600357, baseEnd_600357] using wordTrace_append hprefix tailTrace_600357
  have hstable : (prefixWord ++ tailWord_600357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600357).length < 2 ^ (prefixWord ++ tailWord_600357).sum := by decide
  have hdescent : baseEnd_600357 < baseStart_600357 := by decide
  rcases family_descends (prefixWord ++ tailWord_600357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600372 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_600372 : Nat := 118140960795 + 600372 * 2 ^ 59
def prefixEnd_600372 : Nat := 4983230072969 + 3 ^ 40 * 600372 * 2
def baseEnd_600372 : Nat := 68506535000273394553099

theorem tailTrace_600372 : CollatzResearch.WordTrace tailWord_600372 prefixEnd_600372 68506535000273394553099 := by
  unfold tailWord_600372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10948682890481127109725685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14598243853974836146300913 10948682890481127109725685)
  ·
    refine ⟨1026439020982605666536783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10948682890481127109725685 1026439020982605666536783)
    ·
      refine ⟨1539658531473908499805175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026439020982605666536783 1539658531473908499805175)
      ·
        refine ⟨2309487797210862749707763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539658531473908499805175 2309487797210862749707763)
        ·
          refine ⟨3464231695816294124561645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2309487797210862749707763 3464231695816294124561645)
          ·
            refine ⟨1299086885931110296710617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3464231695816294124561645 1299086885931110296710617)
            ·
              refine ⟨974315164448332722532963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299086885931110296710617 974315164448332722532963)
              ·
                refine ⟨1461472746672499083799445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974315164448332722532963 1461472746672499083799445)
                ·
                  refine ⟨68506535000273394553099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1461472746672499083799445 68506535000273394553099)
                  ·
                    rfl

theorem cell22_600372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_600372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600372 prefixEnd_600372 := by exact prefixLift 600372
  have htrace : WordTrace (prefixWord ++ tailWord_600372) baseStart_600372 baseEnd_600372 := by
    simpa [prefixWord, tailWord_600372, baseEnd_600372] using wordTrace_append hprefix tailTrace_600372
  have hstable : (prefixWord ++ tailWord_600372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600372).length < 2 ^ (prefixWord ++ tailWord_600372).sum := by decide
  have hdescent : baseEnd_600372 < baseStart_600372 := by decide
  rcases family_descends (prefixWord ++ tailWord_600372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600383 : List Nat := [1, 1, 2, 2, 4, 1, 2, 9]
def baseStart_600383 : Nat := 118140960795 + 600383 * 2 ^ 59
def prefixEnd_600383 : Nat := 4983230072969 + 3 ^ 40 * 600383 * 2
def baseEnd_600383 : Nat := 22835930058402202403807

theorem tailTrace_600383 : CollatzResearch.WordTrace tailWord_600383 prefixEnd_600383 22835930058402202403807 := by
  unfold tailWord_600383
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897766983922403098101803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14598511322614935398734535 21897766983922403098101803)
  ·
    refine ⟨32846650475883604647152705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21897766983922403098101803 32846650475883604647152705)
    ·
      refine ⟨24634987856912703485364529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32846650475883604647152705 24634987856912703485364529)
      ·
        refine ⟨18476240892684527614023397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24634987856912703485364529 18476240892684527614023397)
        ·
          refine ⟨3464295167378348927629387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18476240892684527614023397 3464295167378348927629387)
          ·
            refine ⟨5196442751067523391444081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464295167378348927629387 5196442751067523391444081)
            ·
              refine ⟨3897332063300642543583061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5196442751067523391444081 3897332063300642543583061)
              ·
                refine ⟨22835930058402202403807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3897332063300642543583061 22835930058402202403807)
                ·
                  rfl

theorem cell22_600383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 9].length) (baseStart_600383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600383 prefixEnd_600383 := by exact prefixLift 600383
  have htrace : WordTrace (prefixWord ++ tailWord_600383) baseStart_600383 baseEnd_600383 := by
    simpa [prefixWord, tailWord_600383, baseEnd_600383] using wordTrace_append hprefix tailTrace_600383
  have hstable : (prefixWord ++ tailWord_600383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600383).length < 2 ^ (prefixWord ++ tailWord_600383).sum := by decide
  have hdescent : baseEnd_600383 < baseStart_600383 := by decide
  rcases family_descends (prefixWord ++ tailWord_600383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600400 : List Nat := [2, 1, 1, 1, 1, 6, 4, 6]
def baseStart_600400 : Nat := 118140960795 + 600400 * 2 ^ 59
def prefixEnd_600400 : Nat := 4983230072969 + 3 ^ 40 * 600400 * 2
def baseEnd_600400 : Nat := 22836576663670827106579

theorem tailTrace_600400 : CollatzResearch.WordTrace tailWord_600400 prefixEnd_600400 22836576663670827106579 := by
  unfold tailWord_600400
  simp only [CollatzResearch.WordTrace]
  refine ⟨10949193512430407500735327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14598924683240543334313769 10949193512430407500735327)
  ·
    refine ⟨16423790268645611251102991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10949193512430407500735327 16423790268645611251102991)
    ·
      refine ⟨24635685402968416876654487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16423790268645611251102991 24635685402968416876654487)
      ·
        refine ⟨36953528104452625314981731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24635685402968416876654487 36953528104452625314981731)
        ·
          refine ⟨55430292156678937972472597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36953528104452625314981731 55430292156678937972472597)
          ·
            refine ⟨2598294944844325217459653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55430292156678937972472597 2598294944844325217459653)
            ·
              refine ⟨487180302158310978273685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2598294944844325217459653 487180302158310978273685)
              ·
                refine ⟨22836576663670827106579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 487180302158310978273685 22836576663670827106579)
                ·
                  rfl

theorem cell22_600400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_600400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600400 prefixEnd_600400 := by exact prefixLift 600400
  have htrace : WordTrace (prefixWord ++ tailWord_600400) baseStart_600400 baseEnd_600400 := by
    simpa [prefixWord, tailWord_600400, baseEnd_600400] using wordTrace_append hprefix tailTrace_600400
  have hstable : (prefixWord ++ tailWord_600400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600400).length < 2 ^ (prefixWord ++ tailWord_600400).sum := by decide
  have hdescent : baseEnd_600400 < baseStart_600400 := by decide
  rcases family_descends (prefixWord ++ tailWord_600400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600415 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 5, 3]
def baseStart_600415 : Nat := 118140960795 + 600415 * 2 ^ 59
def prefixEnd_600415 : Nat := 4983230072969 + 3 ^ 40 * 600415 * 2
def baseEnd_600415 : Nat := 205534324779582404834165

theorem tailTrace_600415 : CollatzResearch.WordTrace tailWord_600415 prefixEnd_600415 205534324779582404834165 := by
  unfold tailWord_600415
  simp only [CollatzResearch.WordTrace]
  refine ⟨21898934119806472563266699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14599289413204315042177799 21898934119806472563266699)
  ·
    refine ⟨32848401179709708844900049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21898934119806472563266699 32848401179709708844900049)
    ·
      refine ⟨24636300884782281633675037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32848401179709708844900049 24636300884782281633675037)
      ·
        refine ⟨9238612831793355612628139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24636300884782281633675037 9238612831793355612628139)
        ·
          refine ⟨13857919247690033418942209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9238612831793355612628139 13857919247690033418942209)
          ·
            refine ⟨10393439435767525064206657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13857919247690033418942209 10393439435767525064206657)
            ·
              refine ⟨7795079576825643798154993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10393439435767525064206657 7795079576825643798154993)
              ·
                refine ⟨5846309682619232848616245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7795079576825643798154993 5846309682619232848616245)
                ·
                  refine ⟨548091532745553079557773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5846309682619232848616245 548091532745553079557773)
                  ·
                    refine ⟨205534324779582404834165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548091532745553079557773 205534324779582404834165)
                    ·
                      rfl

theorem cell22_600415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_600415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600415 prefixEnd_600415 := by exact prefixLift 600415
  have htrace : WordTrace (prefixWord ++ tailWord_600415) baseStart_600415 baseEnd_600415 := by
    simpa [prefixWord, tailWord_600415, baseEnd_600415] using wordTrace_append hprefix tailTrace_600415
  have hstable : (prefixWord ++ tailWord_600415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600415).length < 2 ^ (prefixWord ++ tailWord_600415).sum := by decide
  have hdescent : baseEnd_600415 < baseStart_600415 := by decide
  rcases family_descends (prefixWord ++ tailWord_600415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600432 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_600432 : Nat := 118140960795 + 600432 * 2 ^ 59
def prefixEnd_600432 : Nat := 4983230072969 + 3 ^ 40 * 600432 * 2
def baseEnd_600432 : Nat := 205540144227000027159113

theorem tailTrace_600432 : CollatzResearch.WordTrace tailWord_600432 prefixEnd_600432 205540144227000027159113 := by
  unfold tailWord_600432
  simp only [CollatzResearch.WordTrace]
  refine ⟨10949777080372442233317775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14599702773829922977757033 10949777080372442233317775)
  ·
    refine ⟨16424665620558663349976663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10949777080372442233317775 16424665620558663349976663)
    ·
      refine ⟨24636998430837995024964995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16424665620558663349976663 24636998430837995024964995)
      ·
        refine ⟨36955497646256992537447493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24636998430837995024964995 36955497646256992537447493)
        ·
          refine ⟨6929155808673186100771405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36955497646256992537447493 6929155808673186100771405)
          ·
            refine ⟨2598433428252444787789277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6929155808673186100771405 2598433428252444787789277)
            ·
              refine ⟨974412535594666795420979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2598433428252444787789277 974412535594666795420979)
              ·
                refine ⟨1461618803392000193131469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974412535594666795420979 1461618803392000193131469)
                ·
                  refine ⟨548107051272000072424301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1461618803392000193131469 548107051272000072424301)
                  ·
                    refine ⟨205540144227000027159113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548107051272000072424301 205540144227000027159113)
                    ·
                      rfl

theorem cell22_600432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_600432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600432 prefixEnd_600432 := by exact prefixLift 600432
  have htrace : WordTrace (prefixWord ++ tailWord_600432) baseStart_600432 baseEnd_600432 := by
    simpa [prefixWord, tailWord_600432, baseEnd_600432] using wordTrace_append hprefix tailTrace_600432
  have hstable : (prefixWord ++ tailWord_600432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600432).length < 2 ^ (prefixWord ++ tailWord_600432).sum := by decide
  have hdescent : baseEnd_600432 < baseStart_600432 := by decide
  rcases family_descends (prefixWord ++ tailWord_600432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600522 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_600522 : Nat := 118140960795 + 600522 * 2 ^ 59
def prefixEnd_600522 : Nat := 4983230072969 + 3 ^ 40 * 600522 * 2
def baseEnd_600522 : Nat := 205570953066269792408837

theorem tailTrace_600522 : CollatzResearch.WordTrace tailWord_600522 prefixEnd_600522 205570953066269792408837 := by
  unfold tailWord_600522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5475709182604707459352955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14601891153612553224941213 5475709182604707459352955)
  ·
    refine ⟨8213563773907061189029433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5475709182604707459352955 8213563773907061189029433)
    ·
      refine ⟨6160172830430295891772075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8213563773907061189029433 6160172830430295891772075)
      ·
        refine ⟨9240259245645443837658113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6160172830430295891772075 9240259245645443837658113)
        ·
          refine ⟨6930194434234082878243585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9240259245645443837658113 6930194434234082878243585)
          ·
            refine ⟨5197645825675562158682689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6930194434234082878243585 5197645825675562158682689)
            ·
              refine ⟨3898234369256671619012017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5197645825675562158682689 3898234369256671619012017)
              ·
                refine ⟨2923675776942503714259013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898234369256671619012017 2923675776942503714259013)
                ·
                  refine ⟨548189208176719446423565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2923675776942503714259013 548189208176719446423565)
                  ·
                    refine ⟨205570953066269792408837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548189208176719446423565 205570953066269792408837)
                    ·
                      rfl

theorem cell22_600522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_600522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600522 prefixEnd_600522 := by exact prefixLift 600522
  have htrace : WordTrace (prefixWord ++ tailWord_600522) baseStart_600522 baseEnd_600522 := by
    simpa [prefixWord, tailWord_600522, baseEnd_600522] using wordTrace_append hprefix tailTrace_600522
  have hstable : (prefixWord ++ tailWord_600522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600522).length < 2 ^ (prefixWord ++ tailWord_600522).sum := by decide
  have hdescent : baseEnd_600522 < baseStart_600522 := by decide
  rcases family_descends (prefixWord ++ tailWord_600522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600597 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 5]
def baseStart_600597 : Nat := 118140960795 + 600597 * 2 ^ 59
def prefixEnd_600597 : Nat := 4983230072969 + 3 ^ 40 * 600597 * 2
def baseEnd_600597 : Nat := 68532209032998198927869

theorem tailTrace_600597 : CollatzResearch.WordTrace tailWord_600597 prefixEnd_600597 68532209032998198927869 := by
  unfold tailWord_600597
  simp only [CollatzResearch.WordTrace]
  refine ⟨21905572205147117646392045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14603714803431411764261363 21905572205147117646392045)
  ·
    refine ⟨8214589576930169117397017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21905572205147117646392045 8214589576930169117397017)
    ·
      refine ⟨6160942182697626838047763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8214589576930169117397017 6160942182697626838047763)
      ·
        refine ⟨9241413274046440257071645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6160942182697626838047763 9241413274046440257071645)
        ·
          refine ⟨3465529977767415096401867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9241413274046440257071645 3465529977767415096401867)
          ·
            refine ⟨5198294966651122644602801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3465529977767415096401867 5198294966651122644602801)
            ·
              refine ⟨3898721224988341983452101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198294966651122644602801 3898721224988341983452101)
              ·
                refine ⟨731010229685314121897269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3898721224988341983452101 731010229685314121897269)
                ·
                  refine ⟨68532209032998198927869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 731010229685314121897269 68532209032998198927869)
                  ·
                    rfl

theorem cell22_600597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_600597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600597 prefixEnd_600597 := by exact prefixLift 600597
  have htrace : WordTrace (prefixWord ++ tailWord_600597) baseStart_600597 baseEnd_600597 := by
    simpa [prefixWord, tailWord_600597, baseEnd_600597] using wordTrace_append hprefix tailTrace_600597
  have hstable : (prefixWord ++ tailWord_600597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600597).length < 2 ^ (prefixWord ++ tailWord_600597).sum := by decide
  have hdescent : baseEnd_600597 < baseStart_600597 := by decide
  rcases family_descends (prefixWord ++ tailWord_600597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600627 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 3, 4]
def baseStart_600627 : Nat := 118140960795 + 600627 * 2 ^ 59
def prefixEnd_600627 : Nat := 4983230072969 + 3 ^ 40 * 600627 * 2
def baseEnd_600627 : Nat := 205606896712084518533515

theorem tailTrace_600627 : CollatzResearch.WordTrace tailWord_600627 prefixEnd_600627 205606896712084518533515 := by
  unfold tailWord_600627
  simp only [CollatzResearch.WordTrace]
  refine ⟨21906666395038432769984135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14604444263358955179989423 21906666395038432769984135)
  ·
    refine ⟨32859999592557649154976203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21906666395038432769984135 32859999592557649154976203)
    ·
      refine ⟨49289999388836473732464305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32859999592557649154976203 49289999388836473732464305)
      ·
        refine ⟨36967499541627355299348229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49289999388836473732464305 36967499541627355299348229)
        ·
          refine ⟨6931406164055129118627793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36967499541627355299348229 6931406164055129118627793)
          ·
            refine ⟨5198554623041346838970845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6931406164055129118627793 5198554623041346838970845)
            ·
              refine ⟨1949457983640505064614067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5198554623041346838970845 1949457983640505064614067)
              ·
                refine ⟨2924186975460757596921101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949457983640505064614067 2924186975460757596921101)
                ·
                  refine ⟨1096570115797784098845413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2924186975460757596921101 1096570115797784098845413)
                  ·
                    refine ⟨205606896712084518533515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096570115797784098845413 205606896712084518533515)
                    ·
                      rfl

theorem cell22_600627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_600627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600627 prefixEnd_600627 := by exact prefixLift 600627
  have htrace : WordTrace (prefixWord ++ tailWord_600627) baseStart_600627 baseEnd_600627 := by
    simpa [prefixWord, tailWord_600627, baseEnd_600627] using wordTrace_append hprefix tailTrace_600627
  have hstable : (prefixWord ++ tailWord_600627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600627).length < 2 ^ (prefixWord ++ tailWord_600627).sum := by decide
  have hdescent : baseEnd_600627 < baseStart_600627 := by decide
  rcases family_descends (prefixWord ++ tailWord_600627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600672 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_600672 : Nat := 118140960795 + 600672 * 2 ^ 59
def prefixEnd_600672 : Nat := 4983230072969 + 3 ^ 40 * 600672 * 2
def baseEnd_600672 : Nat := 205622301131719401158377

theorem tailTrace_600672 : CollatzResearch.WordTrace tailWord_600672 prefixEnd_600672 205622301131719401158377 := by
  unfold tailWord_600672
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954153839937702727686135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14605538453250270303581513 10954153839937702727686135)
  ·
    refine ⟨16431230759906554091529203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10954153839937702727686135 16431230759906554091529203)
    ·
      refine ⟨24646846139859831137293805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16431230759906554091529203 24646846139859831137293805)
      ·
        refine ⟨9242567302447436676485177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24646846139859831137293805 9242567302447436676485177)
        ·
          refine ⟨6931925476835577507363883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9242567302447436676485177 6931925476835577507363883)
          ·
            refine ⟨10397888215253366261045825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931925476835577507363883 10397888215253366261045825)
            ·
              refine ⟨7798416161440024695784369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10397888215253366261045825 7798416161440024695784369)
              ·
                refine ⟨5848812121080018521838277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7798416161440024695784369 5848812121080018521838277)
                ·
                  refine ⟨1096652272702503472844677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5848812121080018521838277 1096652272702503472844677)
                  ·
                    refine ⟨205622301131719401158377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096652272702503472844677 205622301131719401158377)
                    ·
                      rfl

theorem cell22_600672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_600672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600672 prefixEnd_600672 := by exact prefixLift 600672
  have htrace : WordTrace (prefixWord ++ tailWord_600672) baseStart_600672 baseEnd_600672 := by
    simpa [prefixWord, tailWord_600672, baseEnd_600672] using wordTrace_append hprefix tailTrace_600672
  have hstable : (prefixWord ++ tailWord_600672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600672).length < 2 ^ (prefixWord ++ tailWord_600672).sum := by decide
  have hdescent : baseEnd_600672 < baseStart_600672 := by decide
  rcases family_descends (prefixWord ++ tailWord_600672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600693 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 4]
def baseStart_600693 : Nat := 118140960795 + 600693 * 2 ^ 59
def prefixEnd_600693 : Nat := 4983230072969 + 3 ^ 40 * 600693 * 2
def baseEnd_600693 : Nat := 68543163286960782127771

theorem tailTrace_600693 : CollatzResearch.WordTrace tailWord_600693 prefixEnd_600693 68543163286960782127771 := by
  unfold tailWord_600693
  simp only [CollatzResearch.WordTrace]
  refine ⟨21909073612799326041886733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14606049075199550694591155 21909073612799326041886733)
  ·
    refine ⟨8215902604799747265707525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21909073612799326041886733 8215902604799747265707525)
    ·
      refine ⟨1540481738399952612320161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8215902604799747265707525 1540481738399952612320161)
      ·
        refine ⟨1155361303799964459240121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1540481738399952612320161 1155361303799964459240121)
        ·
          refine ⟨866520977849973344430091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155361303799964459240121 866520977849973344430091)
          ·
            refine ⟨1299781466774960016645137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866520977849973344430091 1299781466774960016645137)
            ·
              refine ⟨974836100081220012483853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299781466774960016645137 974836100081220012483853)
              ·
                refine ⟨365563537530457504681445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 974836100081220012483853 365563537530457504681445)
                ·
                  refine ⟨68543163286960782127771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365563537530457504681445 68543163286960782127771)
                  ·
                    rfl

theorem cell22_600693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_600693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600693 prefixEnd_600693 := by exact prefixLift 600693
  have htrace : WordTrace (prefixWord ++ tailWord_600693) baseStart_600693 baseEnd_600693 := by
    simpa [prefixWord, tailWord_600693, baseEnd_600693] using wordTrace_append hprefix tailTrace_600693
  have hstable : (prefixWord ++ tailWord_600693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600693).length < 2 ^ (prefixWord ++ tailWord_600693).sum := by decide
  have hdescent : baseEnd_600693 < baseStart_600693 := by decide
  rcases family_descends (prefixWord ++ tailWord_600693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600708 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_600708 : Nat := 118140960795 + 600708 * 2 ^ 59
def prefixEnd_600708 : Nat := 4983230072969 + 3 ^ 40 * 600708 * 2
def baseEnd_600708 : Nat := 205634624667427307258267

theorem tailTrace_600708 : CollatzResearch.WordTrace tailWord_600708 prefixEnd_600708 205634624667427307258267 := by
  unfold tailWord_600708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954810353872491801841389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14606413805163322402455185 10954810353872491801841389)
  ·
    refine ⟨4108053882702184425690521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10954810353872491801841389 4108053882702184425690521)
    ·
      refine ⟨3081040412026638319267891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4108053882702184425690521 3081040412026638319267891)
      ·
        refine ⟨4621560618039957478901837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3081040412026638319267891 4621560618039957478901837)
        ·
          refine ⟨1733085231764984054588189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4621560618039957478901837 1733085231764984054588189)
          ·
            refine ⟨649906961911869020470571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1733085231764984054588189 649906961911869020470571)
            ·
              refine ⟨974860442867803530705857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649906961911869020470571 974860442867803530705857)
              ·
                refine ⟨731145332150852648029393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974860442867803530705857 731145332150852648029393)
                ·
                  refine ⟨548358999113139486022045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 731145332150852648029393 548358999113139486022045)
                  ·
                    refine ⟨205634624667427307258267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548358999113139486022045 205634624667427307258267)
                    ·
                      rfl

theorem cell22_600708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_600708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600708 prefixEnd_600708 := by exact prefixLift 600708
  have htrace : WordTrace (prefixWord ++ tailWord_600708) baseStart_600708 baseEnd_600708 := by
    simpa [prefixWord, tailWord_600708, baseEnd_600708] using wordTrace_append hprefix tailTrace_600708
  have hstable : (prefixWord ++ tailWord_600708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600708).length < 2 ^ (prefixWord ++ tailWord_600708).sum := by decide
  have hdescent : baseEnd_600708 < baseStart_600708 := by decide
  rcases family_descends (prefixWord ++ tailWord_600708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600749 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 7]
def baseStart_600749 : Nat := 118140960795 + 600749 * 2 ^ 59
def prefixEnd_600749 : Nat := 4983230072969 + 3 ^ 40 * 600749 * 2
def baseEnd_600749 : Nat := 68549553268438955661047

theorem tailTrace_600749 : CollatzResearch.WordTrace tailWord_600749 prefixEnd_600749 68549553268438955661047 := by
  unfold tailWord_600749
  simp only [CollatzResearch.WordTrace]
  refine ⟨21911116100596447605925301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14607410733730965070616867 21911116100596447605925301)
  ·
    refine ⟨2054167134430916963055497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21911116100596447605925301 2054167134430916963055497)
    ·
      refine ⟨1540625350823187722291623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2054167134430916963055497 1540625350823187722291623)
      ·
        refine ⟨2310938026234781583437435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540625350823187722291623 2310938026234781583437435)
        ·
          refine ⟨3466407039352172375156153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310938026234781583437435 3466407039352172375156153)
          ·
            refine ⟨2599805279514129281367115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466407039352172375156153 2599805279514129281367115)
            ·
              refine ⟨3899707919271193922050673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599805279514129281367115 3899707919271193922050673)
              ·
                refine ⟨2924780939453395441538005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899707919271193922050673 2924780939453395441538005)
                ·
                  refine ⟨68549553268438955661047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2924780939453395441538005 68549553268438955661047)
                  ·
                    rfl

theorem cell22_600749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_600749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600749 prefixEnd_600749 := by exact prefixLift 600749
  have htrace : WordTrace (prefixWord ++ tailWord_600749) baseStart_600749 baseEnd_600749 := by
    simpa [prefixWord, tailWord_600749, baseEnd_600749] using wordTrace_append hprefix tailTrace_600749
  have hstable : (prefixWord ++ tailWord_600749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600749).length < 2 ^ (prefixWord ++ tailWord_600749).sum := by decide
  have hdescent : baseEnd_600749 < baseStart_600749 := by decide
  rcases family_descends (prefixWord ++ tailWord_600749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600809 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_600809 : Nat := 118140960795 + 600809 * 2 ^ 59
def prefixEnd_600809 : Nat := 4983230072969 + 3 ^ 40 * 600809 * 2
def baseEnd_600809 : Nat := 205669199031496710482957

theorem tailTrace_600809 : CollatzResearch.WordTrace tailWord_600809 prefixEnd_600809 205669199031496710482957 := by
  unfold tailWord_600809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21913304480379077853109481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14608869653586051902072987 21913304480379077853109481)
  ·
    refine ⟨16434978360284308389832111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21913304480379077853109481 16434978360284308389832111)
    ·
      refine ⟨24652467540426462584748167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16434978360284308389832111 24652467540426462584748167)
      ·
        refine ⟨36978701310639693877122251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24652467540426462584748167 36978701310639693877122251)
        ·
          refine ⟨55468051965959540815683377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36978701310639693877122251 55468051965959540815683377)
          ·
            refine ⟨41601038974469655611762533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55468051965959540815683377 41601038974469655611762533)
            ·
              refine ⟨7800194807713060427205475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41601038974469655611762533 7800194807713060427205475)
              ·
                refine ⟨11700292211569590640808213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7800194807713060427205475 11700292211569590640808213)
                ·
                  refine ⟨548451197417324561287885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11700292211569590640808213 548451197417324561287885)
                  ·
                    refine ⟨205669199031496710482957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548451197417324561287885 205669199031496710482957)
                    ·
                      rfl

theorem cell22_600809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_600809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600809 prefixEnd_600809 := by exact prefixLift 600809
  have htrace : WordTrace (prefixWord ++ tailWord_600809) baseStart_600809 baseEnd_600809 := by
    simpa [prefixWord, tailWord_600809, baseEnd_600809] using wordTrace_append hprefix tailTrace_600809
  have hstable : (prefixWord ++ tailWord_600809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600809).length < 2 ^ (prefixWord ++ tailWord_600809).sum := by decide
  have hdescent : baseEnd_600809 < baseStart_600809 := by decide
  rcases family_descends (prefixWord ++ tailWord_600809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600813 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_600813 : Nat := 118140960795 + 600813 * 2 ^ 59
def prefixEnd_600813 : Nat := 4983230072969 + 3 ^ 40 * 600813 * 2
def baseEnd_600813 : Nat := 205670568313242033382945

theorem tailTrace_600813 : CollatzResearch.WordTrace tailWord_600813 prefixEnd_600813 205670568313242033382945 := by
  unfold tailWord_600813
  simp only [CollatzResearch.WordTrace]
  refine ⟨21913450372364586536255093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14608966914909724357503395 21913450372364586536255093)
  ·
    refine ⟨2054385972409179987773915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21913450372364586536255093 2054385972409179987773915)
    ·
      refine ⟨3081578958613769981660873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2054385972409179987773915 3081578958613769981660873)
      ·
        refine ⟨2311184218960327486245655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3081578958613769981660873 2311184218960327486245655)
        ·
          refine ⟨3466776328440491229368483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311184218960327486245655 3466776328440491229368483)
          ·
            refine ⟨5200164492660736844052725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466776328440491229368483 5200164492660736844052725)
            ·
              refine ⟨487515421186944079129943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5200164492660736844052725 487515421186944079129943)
              ·
                refine ⟨731273131780416118694915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487515421186944079129943 731273131780416118694915)
                ·
                  refine ⟨1096909697670624178042373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731273131780416118694915 1096909697670624178042373)
                  ·
                    refine ⟨205670568313242033382945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096909697670624178042373 205670568313242033382945)
                    ·
                      rfl

theorem cell22_600813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_600813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600813 prefixEnd_600813 := by exact prefixLift 600813
  have htrace : WordTrace (prefixWord ++ tailWord_600813) baseStart_600813 baseEnd_600813 := by
    simpa [prefixWord, tailWord_600813, baseEnd_600813] using wordTrace_append hprefix tailTrace_600813
  have hstable : (prefixWord ++ tailWord_600813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600813).length < 2 ^ (prefixWord ++ tailWord_600813).sum := by decide
  have hdescent : baseEnd_600813 < baseStart_600813 := by decide
  rcases family_descends (prefixWord ++ tailWord_600813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600821 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_600821 : Nat := 118140960795 + 600821 * 2 ^ 59
def prefixEnd_600821 : Nat := 4983230072969 + 3 ^ 40 * 600821 * 2
def baseEnd_600821 : Nat := 205673306876732679182921

theorem tailTrace_600821 : CollatzResearch.WordTrace tailWord_600821 prefixEnd_600821 205673306876732679182921 := by
  unfold tailWord_600821
  simp only [CollatzResearch.WordTrace]
  refine ⟨21913742156335603902546317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14609161437557069268364211 21913742156335603902546317)
  ·
    refine ⟨8217653308625851463454869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21913742156335603902546317 8217653308625851463454869)
    ·
      refine ⟨385202498841836787349447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8217653308625851463454869 385202498841836787349447)
      ·
        refine ⟨577803748262755181024171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385202498841836787349447 577803748262755181024171)
        ·
          refine ⟨866705622394132771536257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577803748262755181024171 866705622394132771536257)
          ·
            refine ⟨650029216795599578652193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866705622394132771536257 650029216795599578652193)
            ·
              refine ⟨487521912596699683989145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650029216795599578652193 487521912596699683989145)
              ·
                refine ⟨365641434447524762991859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487521912596699683989145 365641434447524762991859)
                ·
                  refine ⟨548462151671287144487789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365641434447524762991859 548462151671287144487789)
                  ·
                    refine ⟨205673306876732679182921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548462151671287144487789 205673306876732679182921)
                    ·
                      rfl

theorem cell22_600821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_600821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600821 prefixEnd_600821 := by exact prefixLift 600821
  have htrace : WordTrace (prefixWord ++ tailWord_600821) baseStart_600821 baseEnd_600821 := by
    simpa [prefixWord, tailWord_600821, baseEnd_600821] using wordTrace_append hprefix tailTrace_600821
  have hstable : (prefixWord ++ tailWord_600821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600821).length < 2 ^ (prefixWord ++ tailWord_600821).sum := by decide
  have hdescent : baseEnd_600821 < baseStart_600821 := by decide
  rcases family_descends (prefixWord ++ tailWord_600821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600824 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_600824 : Nat := 118140960795 + 600824 * 2 ^ 59
def prefixEnd_600824 : Nat := 4983230072969 + 3 ^ 40 * 600824 * 2
def baseEnd_600824 : Nat := 205674333838041671357911

theorem tailTrace_600824 : CollatzResearch.WordTrace tailWord_600824 prefixEnd_600824 205674333838041671357911 := by
  unfold tailWord_600824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956925787662367707452763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14609234383549823609937017 10956925787662367707452763)
  ·
    refine ⟨16435388681493551561179145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10956925787662367707452763 16435388681493551561179145)
    ·
      refine ⟨12326541511120163670884359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16435388681493551561179145 12326541511120163670884359)
      ·
        refine ⟨18489812266680245506326539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12326541511120163670884359 18489812266680245506326539)
        ·
          refine ⟨27734718400020368259489809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18489812266680245506326539 27734718400020368259489809)
          ·
            refine ⟨20801038800015276194617357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27734718400020368259489809 20801038800015276194617357)
            ·
              refine ⟨7800389550005728572981509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20801038800015276194617357 7800389550005728572981509)
              ·
                refine ⟨1462573040626074107434033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7800389550005728572981509 1462573040626074107434033)
                ·
                  refine ⟨1096929780469555580575525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1462573040626074107434033 1096929780469555580575525)
                  ·
                    refine ⟨205674333838041671357911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096929780469555580575525 205674333838041671357911)
                    ·
                      rfl

theorem cell22_600824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_600824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600824 prefixEnd_600824 := by exact prefixLift 600824
  have htrace : WordTrace (prefixWord ++ tailWord_600824) baseStart_600824 baseEnd_600824 := by
    simpa [prefixWord, tailWord_600824, baseEnd_600824] using wordTrace_append hprefix tailTrace_600824
  have hstable : (prefixWord ++ tailWord_600824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600824).length < 2 ^ (prefixWord ++ tailWord_600824).sum := by decide
  have hdescent : baseEnd_600824 < baseStart_600824 := by decide
  rcases family_descends (prefixWord ++ tailWord_600824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600826 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_600826 : Nat := 118140960795 + 600826 * 2 ^ 59
def prefixEnd_600826 : Nat := 4983230072969 + 3 ^ 40 * 600826 * 2
def baseEnd_600826 : Nat := 205675018478914332807905

theorem tailTrace_600826 : CollatzResearch.WordTrace tailWord_600826 prefixEnd_600826 205675018478914332807905 := by
  unfold tailWord_600826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478481130329372439119583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14609283014211659837652221 5478481130329372439119583)
  ·
    refine ⟨8217721695494058658679375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5478481130329372439119583 8217721695494058658679375)
    ·
      refine ⟨12326582543241087988019063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8217721695494058658679375 12326582543241087988019063)
      ·
        refine ⟨18489873814861631982028595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12326582543241087988019063 18489873814861631982028595)
        ·
          refine ⟨27734810722292447973042893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18489873814861631982028595 27734810722292447973042893)
          ·
            refine ⟨10400554020859667989891085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27734810722292447973042893 10400554020859667989891085)
            ·
              refine ⟨3900207757822375496209157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10400554020859667989891085 3900207757822375496209157)
              ·
                refine ⟨731288954591695405539217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3900207757822375496209157 731288954591695405539217)
                ·
                  refine ⟨548466715943771554154413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 731288954591695405539217 548466715943771554154413)
                  ·
                    refine ⟨205675018478914332807905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548466715943771554154413 205675018478914332807905)
                    ·
                      rfl

theorem cell22_600826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_600826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600826 prefixEnd_600826 := by exact prefixLift 600826
  have htrace : WordTrace (prefixWord ++ tailWord_600826) baseStart_600826 baseEnd_600826 := by
    simpa [prefixWord, tailWord_600826, baseEnd_600826] using wordTrace_append hprefix tailTrace_600826
  have hstable : (prefixWord ++ tailWord_600826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600826).length < 2 ^ (prefixWord ++ tailWord_600826).sum := by decide
  have hdescent : baseEnd_600826 < baseStart_600826 := by decide
  rcases family_descends (prefixWord ++ tailWord_600826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600828 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 4]
def baseStart_600828 : Nat := 118140960795 + 600828 * 2 ^ 59
def prefixEnd_600828 : Nat := 4983230072969 + 3 ^ 40 * 600828 * 2
def baseEnd_600828 : Nat := 68558567706595664752633

theorem tailTrace_600828 : CollatzResearch.WordTrace tailWord_600828 prefixEnd_600828 68558567706595664752633 := by
  unfold tailWord_600828
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956998733655122049025569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14609331644873496065367425 10956998733655122049025569)
  ·
    refine ⟨8217749050241341536769177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10956998733655122049025569 8217749050241341536769177)
    ·
      refine ⟨6163311787681006152576883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8217749050241341536769177 6163311787681006152576883)
      ·
        refine ⟨9244967681521509228865325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6163311787681006152576883 9244967681521509228865325)
        ·
          refine ⟨3466862880570565960824497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9244967681521509228865325 3466862880570565960824497)
          ·
            refine ⟨2600147160427924470618373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466862880570565960824497 2600147160427924470618373)
            ·
              refine ⟨487527592580235838240945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2600147160427924470618373 487527592580235838240945)
              ·
                refine ⟨365645694435176878680709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487527592580235838240945 365645694435176878680709)
                ·
                  refine ⟨68558567706595664752633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365645694435176878680709 68558567706595664752633)
                  ·
                    rfl

theorem cell22_600828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_600828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600828 prefixEnd_600828 := by exact prefixLift 600828
  have htrace : WordTrace (prefixWord ++ tailWord_600828) baseStart_600828 baseEnd_600828 := by
    simpa [prefixWord, tailWord_600828, baseEnd_600828] using wordTrace_append hprefix tailTrace_600828
  have hstable : (prefixWord ++ tailWord_600828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600828).length < 2 ^ (prefixWord ++ tailWord_600828).sum := by decide
  have hdescent : baseEnd_600828 < baseStart_600828 := by decide
  rcases family_descends (prefixWord ++ tailWord_600828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600888 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 1, 3]
def baseStart_600888 : Nat := 118140960795 + 600888 * 2 ^ 59
def prefixEnd_600888 : Nat := 4983230072969 + 3 ^ 40 * 600888 * 2
def baseEnd_600888 : Nat := 205696242345966837757715

theorem tailTrace_600888 : CollatzResearch.WordTrace tailWord_600888 prefixEnd_600888 205696242345966837757715 := by
  unfold tailWord_600888
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958092923546437172617659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14610790564728582896823545 10958092923546437172617659)
  ·
    refine ⟨16437139385319655758926489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10958092923546437172617659 16437139385319655758926489)
    ·
      refine ⟨12327854538989741819194867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16437139385319655758926489 12327854538989741819194867)
      ·
        refine ⟨18491781808484612728792301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12327854538989741819194867 18491781808484612728792301)
        ·
          refine ⟨6934418178181729773297113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18491781808484612728792301 6934418178181729773297113)
          ·
            refine ⟨5200813633636297329972835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6934418178181729773297113 5200813633636297329972835)
            ·
              refine ⟨7801220450454445994959253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200813633636297329972835 7801220450454445994959253)
              ·
                refine ⟨365682208615052156013715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7801220450454445994959253 365682208615052156013715)
                ·
                  refine ⟨548523312922578234020573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365682208615052156013715 548523312922578234020573)
                  ·
                    refine ⟨205696242345966837757715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548523312922578234020573 205696242345966837757715)
                    ·
                      rfl

theorem cell22_600888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_600888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600888 prefixEnd_600888 := by exact prefixLift 600888
  have htrace : WordTrace (prefixWord ++ tailWord_600888) baseStart_600888 baseEnd_600888 := by
    simpa [prefixWord, tailWord_600888, baseEnd_600888] using wordTrace_append hprefix tailTrace_600888
  have hstable : (prefixWord ++ tailWord_600888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600888).length < 2 ^ (prefixWord ++ tailWord_600888).sum := by decide
  have hdescent : baseEnd_600888 < baseStart_600888 := by decide
  rcases family_descends (prefixWord ++ tailWord_600888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600899 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_600899 : Nat := 118140960795 + 600899 * 2 ^ 59
def prefixEnd_600899 : Nat := 4983230072969 + 3 ^ 40 * 600899 * 2
def baseEnd_600899 : Nat := 205700007870766475732681

theorem tailTrace_600899 : CollatzResearch.WordTrace tailWord_600899 prefixEnd_600899 205700007870766475732681 := by
  unfold tailWord_600899
  simp only [CollatzResearch.WordTrace]
  refine ⟨21916587050053023223885751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14611058033368682149257167 21916587050053023223885751)
  ·
    refine ⟨32874880575079534835828627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21916587050053023223885751 32874880575079534835828627)
    ·
      refine ⟨49312320862619302253742941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32874880575079534835828627 49312320862619302253742941)
      ·
        refine ⟨18492120323482238345153603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49312320862619302253742941 18492120323482238345153603)
        ·
          refine ⟨27738180485223357517730405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18492120323482238345153603 27738180485223357517730405)
          ·
            refine ⟨5200908840979379534574451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27738180485223357517730405 5200908840979379534574451)
            ·
              refine ⟨7801363261469069301861677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200908840979379534574451 7801363261469069301861677)
              ·
                refine ⟨2925511223050900988198129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7801363261469069301861677 2925511223050900988198129)
                ·
                  refine ⟨2194133417288175741148597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925511223050900988198129 2194133417288175741148597)
                  ·
                    refine ⟨205700007870766475732681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2194133417288175741148597 205700007870766475732681)
                    ·
                      rfl

theorem cell22_600899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_600899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600899 prefixEnd_600899 := by exact prefixLift 600899
  have htrace : WordTrace (prefixWord ++ tailWord_600899) baseStart_600899 baseEnd_600899 := by
    simpa [prefixWord, tailWord_600899, baseEnd_600899] using wordTrace_append hprefix tailTrace_600899
  have hstable : (prefixWord ++ tailWord_600899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600899).length < 2 ^ (prefixWord ++ tailWord_600899).sum := by decide
  have hdescent : baseEnd_600899 < baseStart_600899 := by decide
  rcases family_descends (prefixWord ++ tailWord_600899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600946 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_600946 : Nat := 118140960795 + 600946 * 2 ^ 59
def prefixEnd_600946 : Nat := 4983230072969 + 3 ^ 40 * 600946 * 2
def baseEnd_600946 : Nat := 68572032310424673269179

theorem tailTrace_600946 : CollatzResearch.WordTrace tailWord_600946 prefixEnd_600946 68572032310424673269179 := by
  unfold tailWord_600946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479575320220687562711673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14612200853921833500564461 5479575320220687562711673)
  ·
    refine ⟨4109681490165515672033755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5479575320220687562711673 4109681490165515672033755)
    ·
      refine ⟨6164522235248273508050633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4109681490165515672033755 6164522235248273508050633)
      ·
        refine ⟨4623391676436205131037975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6164522235248273508050633 4623391676436205131037975)
        ·
          refine ⟨6935087514654307696556963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623391676436205131037975 6935087514654307696556963)
          ·
            refine ⟨10402631271981461544835445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6935087514654307696556963 10402631271981461544835445)
            ·
              refine ⟨975246681748262019828323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10402631271981461544835445 975246681748262019828323)
              ·
                refine ⟨1462870022622393029742485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975246681748262019828323 1462870022622393029742485)
                ·
                  refine ⟨68572032310424673269179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1462870022622393029742485 68572032310424673269179)
                  ·
                    rfl

theorem cell22_600946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_600946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600946 prefixEnd_600946 := by exact prefixLift 600946
  have htrace : WordTrace (prefixWord ++ tailWord_600946) baseStart_600946 baseEnd_600946 := by
    simpa [prefixWord, tailWord_600946, baseEnd_600946] using wordTrace_append hprefix tailTrace_600946
  have hstable : (prefixWord ++ tailWord_600946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600946).length < 2 ^ (prefixWord ++ tailWord_600946).sum := by decide
  have hdescent : baseEnd_600946 < baseStart_600946 := by decide
  rcases family_descends (prefixWord ++ tailWord_600946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600959 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_600959 : Nat := 118140960795 + 600959 * 2 ^ 59
def prefixEnd_600959 : Nat := 4983230072969 + 3 ^ 40 * 600959 * 2
def baseEnd_600959 : Nat := 205720547096946319232497

theorem tailTrace_600959 : CollatzResearch.WordTrace tailWord_600959 prefixEnd_600959 205720547096946319232497 := by
  unfold tailWord_600959
  simp only [CollatzResearch.WordTrace]
  refine ⟨21918775429835653471069931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14612516953223768980713287 21918775429835653471069931)
  ·
    refine ⟨32878163144753480206604897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21918775429835653471069931 32878163144753480206604897)
    ·
      refine ⟨24658622358565110154953673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32878163144753480206604897 24658622358565110154953673)
      ·
        refine ⟨18493966768923832616215255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24658622358565110154953673 18493966768923832616215255)
        ·
          refine ⟨27740950153385748924322883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18493966768923832616215255 27740950153385748924322883)
          ·
            refine ⟨41611425230078623386484325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27740950153385748924322883 41611425230078623386484325)
            ·
              refine ⟨7802142230639741884965811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41611425230078623386484325 7802142230639741884965811)
              ·
                refine ⟨11703213345959612827448717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7802142230639741884965811 11703213345959612827448717)
                ·
                  refine ⟨4388705004734854810293269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11703213345959612827448717 4388705004734854810293269)
                  ·
                    refine ⟨205720547096946319232497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4388705004734854810293269 205720547096946319232497)
                    ·
                      rfl

theorem cell22_600959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_600959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600959 prefixEnd_600959 := by exact prefixLift 600959
  have htrace : WordTrace (prefixWord ++ tailWord_600959) baseStart_600959 baseEnd_600959 := by
    simpa [prefixWord, tailWord_600959, baseEnd_600959] using wordTrace_append hprefix tailTrace_600959
  have hstable : (prefixWord ++ tailWord_600959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600959).length < 2 ^ (prefixWord ++ tailWord_600959).sum := by decide
  have hdescent : baseEnd_600959 < baseStart_600959 := by decide
  rcases family_descends (prefixWord ++ tailWord_600959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600993 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_600993 : Nat := 118140960795 + 600993 * 2 ^ 59
def prefixEnd_600993 : Nat := 4983230072969 + 3 ^ 40 * 600993 * 2
def baseEnd_600993 : Nat := 205732185991781563882393

theorem tailTrace_600993 : CollatzResearch.WordTrace tailWord_600993 prefixEnd_600993 205732185991781563882393 := by
  unfold tailWord_600993
  simp only [CollatzResearch.WordTrace]
  refine ⟨21920015511712477277807633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14613343674474984851871755 21920015511712477277807633)
  ·
    refine ⟨16440011633784357958355725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21920015511712477277807633 16440011633784357958355725)
    ·
      refine ⟨6165004362669134234383397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16440011633784357958355725 6165004362669134234383397)
      ·
        refine ⟨1155938318000462668946887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6165004362669134234383397 1155938318000462668946887)
        ·
          refine ⟨1733907477000694003420331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155938318000462668946887 1733907477000694003420331)
          ·
            refine ⟨2600861215501041005130497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733907477000694003420331 2600861215501041005130497)
            ·
              refine ⟨1950645911625780753847873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600861215501041005130497 1950645911625780753847873)
              ·
                refine ⟨1462984433719335565385905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950645911625780753847873 1462984433719335565385905)
                ·
                  refine ⟨1097238325289501674039429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1462984433719335565385905 1097238325289501674039429)
                  ·
                    refine ⟨205732185991781563882393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097238325289501674039429 205732185991781563882393)
                    ·
                      rfl

theorem cell22_600993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_600993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_600993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_600993 prefixEnd_600993 := by exact prefixLift 600993
  have htrace : WordTrace (prefixWord ++ tailWord_600993) baseStart_600993 baseEnd_600993 := by
    simpa [prefixWord, tailWord_600993, baseEnd_600993] using wordTrace_append hprefix tailTrace_600993
  have hstable : (prefixWord ++ tailWord_600993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600993).length < 2 ^ (prefixWord ++ tailWord_600993).sum := by decide
  have hdescent : baseEnd_600993 < baseStart_600993 := by decide
  rcases family_descends (prefixWord ++ tailWord_600993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601012 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_601012 : Nat := 118140960795 + 601012 * 2 ^ 59
def prefixEnd_601012 : Nat := 4983230072969 + 3 ^ 40 * 601012 * 2
def baseEnd_601012 : Nat := 205738690080071847657335

theorem tailTrace_601012 : CollatzResearch.WordTrace tailWord_601012 prefixEnd_601012 205738690080071847657335 := by
  unfold tailWord_601012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960354249321821761374645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14613805665762429015166193 10960354249321821761374645)
  ·
    refine ⟨1027533210873920790128873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10960354249321821761374645 1027533210873920790128873)
    ·
      refine ⟨770649908155440592596655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1027533210873920790128873 770649908155440592596655)
      ·
        refine ⟨1155974862233160888894983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770649908155440592596655 1155974862233160888894983)
        ·
          refine ⟨1733962293349741333342475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155974862233160888894983 1733962293349741333342475)
          ·
            refine ⟨2600943440024612000013713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733962293349741333342475 2600943440024612000013713)
            ·
              refine ⟨1950707580018459000010285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600943440024612000013713 1950707580018459000010285)
              ·
                refine ⟨731515342506922125003857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1950707580018459000010285 731515342506922125003857)
                ·
                  refine ⟨548636506880191593752893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 731515342506922125003857 548636506880191593752893)
                  ·
                    refine ⟨205738690080071847657335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548636506880191593752893 205738690080071847657335)
                    ·
                      rfl

theorem cell22_601012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_601012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601012 prefixEnd_601012 := by exact prefixLift 601012
  have htrace : WordTrace (prefixWord ++ tailWord_601012) baseStart_601012 baseEnd_601012 := by
    simpa [prefixWord, tailWord_601012, baseEnd_601012] using wordTrace_append hprefix tailTrace_601012
  have hstable : (prefixWord ++ tailWord_601012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601012).length < 2 ^ (prefixWord ++ tailWord_601012).sum := by decide
  have hdescent : baseEnd_601012 < baseStart_601012 := by decide
  rcases family_descends (prefixWord ++ tailWord_601012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601036 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_601036 : Nat := 118140960795 + 601036 * 2 ^ 59
def prefixEnd_601036 : Nat := 4983230072969 + 3 ^ 40 * 601036 * 2
def baseEnd_601036 : Nat := 68582301923514595019087

theorem tailTrace_601036 : CollatzResearch.WordTrace tailWord_601036 prefixEnd_601036 68582301923514595019087 := by
  unfold tailWord_601036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960791925278347810811481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14614389233704463747748641 10960791925278347810811481)
  ·
    refine ⟨8220593943958760858108611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10960791925278347810811481 8220593943958760858108611)
    ·
      refine ⟨12330890915938141287162917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8220593943958760858108611 12330890915938141287162917)
      ·
        refine ⟨2312042046738401491343047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12330890915938141287162917 2312042046738401491343047)
        ·
          refine ⟨3468063070107602237014571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312042046738401491343047 3468063070107602237014571)
          ·
            refine ⟨5202094605161403355521857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468063070107602237014571 5202094605161403355521857)
            ·
              refine ⟨3901570953871052516641393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202094605161403355521857 3901570953871052516641393)
              ·
                refine ⟨2926178215403289387481045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901570953871052516641393 2926178215403289387481045)
                ·
                  refine ⟨68582301923514595019087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2926178215403289387481045 68582301923514595019087)
                  ·
                    rfl

theorem cell22_601036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_601036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601036 prefixEnd_601036 := by exact prefixLift 601036
  have htrace : WordTrace (prefixWord ++ tailWord_601036) baseStart_601036 baseEnd_601036 := by
    simpa [prefixWord, tailWord_601036, baseEnd_601036] using wordTrace_append hprefix tailTrace_601036
  have hstable : (prefixWord ++ tailWord_601036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601036).length < 2 ^ (prefixWord ++ tailWord_601036).sum := by decide
  have hdescent : baseEnd_601036 < baseStart_601036 := by decide
  rcases family_descends (prefixWord ++ tailWord_601036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601053 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 7]
def baseStart_601053 : Nat := 118140960795 + 601053 * 2 ^ 59
def prefixEnd_601053 : Nat := 4983230072969 + 3 ^ 40 * 601053 * 2
def baseEnd_601053 : Nat := 68584241739320469127403

theorem tailTrace_601053 : CollatzResearch.WordTrace tailWord_601053 prefixEnd_601053 68584241739320469127403 := by
  unfold tailWord_601053
  simp only [CollatzResearch.WordTrace]
  refine ⟨21922203891495107524991813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14614802594330071683327875 21922203891495107524991813)
  ·
    refine ⟨4110413229655332660935965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21922203891495107524991813 4110413229655332660935965)
    ·
      refine ⟨1541404961120749747850987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4110413229655332660935965 1541404961120749747850987)
      ·
        refine ⟨2312107441681124621776481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541404961120749747850987 2312107441681124621776481)
        ·
          refine ⟨1734080581260843466332361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312107441681124621776481 1734080581260843466332361)
          ·
            refine ⟨1300560435945632599749271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734080581260843466332361 1300560435945632599749271)
            ·
              refine ⟨1950840653918448899623907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300560435945632599749271 1950840653918448899623907)
              ·
                refine ⟨2926260980877673349435861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950840653918448899623907 2926260980877673349435861)
                ·
                  refine ⟨68584241739320469127403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2926260980877673349435861 68584241739320469127403)
                  ·
                    rfl

theorem cell22_601053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_601053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601053 prefixEnd_601053 := by exact prefixLift 601053
  have htrace : WordTrace (prefixWord ++ tailWord_601053) baseStart_601053 baseEnd_601053 := by
    simpa [prefixWord, tailWord_601053, baseEnd_601053] using wordTrace_append hprefix tailTrace_601053
  have hstable : (prefixWord ++ tailWord_601053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601053).length < 2 ^ (prefixWord ++ tailWord_601053).sum := by decide
  have hdescent : baseEnd_601053 < baseStart_601053 := by decide
  rcases family_descends (prefixWord ++ tailWord_601053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601076 : List Nat := [2, 6, 2, 1, 1, 2, 2, 6]
def baseStart_601076 : Nat := 118140960795 + 601076 * 2 ^ 59
def prefixEnd_601076 : Nat := 4983230072969 + 3 ^ 40 * 601076 * 2
def baseEnd_601076 : Nat := 22862288731999668228571

theorem tailTrace_601076 : CollatzResearch.WordTrace tailWord_601076 prefixEnd_601076 22862288731999668228571 := by
  unfold tailWord_601076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10961521385205891226539541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14615361846941188302052721 10961521385205891226539541)
  ·
    refine ⟨513821314931526151244041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10961521385205891226539541 513821314931526151244041)
    ·
      refine ⟨385365986198644613433031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 513821314931526151244041 385365986198644613433031)
      ·
        refine ⟨578048979297966920149547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385365986198644613433031 578048979297966920149547)
        ·
          refine ⟨867073468946950380224321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578048979297966920149547 867073468946950380224321)
          ·
            refine ⟨650305101710212785168241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867073468946950380224321 650305101710212785168241)
            ·
              refine ⟨487728826282659588876181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650305101710212785168241 487728826282659588876181)
              ·
                refine ⟨22862288731999668228571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 487728826282659588876181 22862288731999668228571)
                ·
                  rfl

theorem cell22_601076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 6].length) (baseStart_601076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601076 prefixEnd_601076 := by exact prefixLift 601076
  have htrace : WordTrace (prefixWord ++ tailWord_601076) baseStart_601076 baseEnd_601076 := by
    simpa [prefixWord, tailWord_601076, baseEnd_601076] using wordTrace_append hprefix tailTrace_601076
  have hstable : (prefixWord ++ tailWord_601076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601076).length < 2 ^ (prefixWord ++ tailWord_601076).sum := by decide
  have hdescent : baseEnd_601076 < baseStart_601076 := by decide
  rcases family_descends (prefixWord ++ tailWord_601076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601081 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 6]
def baseStart_601081 : Nat := 118140960795 + 601081 * 2 ^ 59
def prefixEnd_601081 : Nat := 4983230072969 + 3 ^ 40 * 601081 * 2
def baseEnd_601081 : Nat := 68587436730059555894041

theorem tailTrace_601081 : CollatzResearch.WordTrace tailWord_601081 prefixEnd_601081 68587436730059555894041 := by
  unfold tailWord_601081
  simp only [CollatzResearch.WordTrace]
  refine ⟨21923225135393668307011097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14615483423595778871340731 21923225135393668307011097)
  ·
    refine ⟨16442418851545251230258323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21923225135393668307011097 16442418851545251230258323)
    ·
      refine ⟨24663628277317876845387485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16442418851545251230258323 24663628277317876845387485)
      ·
        refine ⟨9248860603994203817020307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24663628277317876845387485 9248860603994203817020307)
        ·
          refine ⟨13873290905991305725530461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9248860603994203817020307 13873290905991305725530461)
          ·
            refine ⟨5202484089746739647073923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13873290905991305725530461 5202484089746739647073923)
            ·
              refine ⟨7803726134620109470610885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202484089746739647073923 7803726134620109470610885)
              ·
                refine ⟨1463198650241270525739541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7803726134620109470610885 1463198650241270525739541)
                ·
                  refine ⟨68587436730059555894041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1463198650241270525739541 68587436730059555894041)
                  ·
                    rfl

theorem cell22_601081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_601081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601081 prefixEnd_601081 := by exact prefixLift 601081
  have htrace : WordTrace (prefixWord ++ tailWord_601081) baseStart_601081 baseEnd_601081 := by
    simpa [prefixWord, tailWord_601081, baseEnd_601081] using wordTrace_append hprefix tailTrace_601081
  have hstable : (prefixWord ++ tailWord_601081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601081).length < 2 ^ (prefixWord ++ tailWord_601081).sum := by decide
  have hdescent : baseEnd_601081 < baseStart_601081 := by decide
  rcases family_descends (prefixWord ++ tailWord_601081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601113 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_601113 : Nat := 118140960795 + 601113 * 2 ^ 59
def prefixEnd_601113 : Nat := 4983230072969 + 3 ^ 40 * 601113 * 2
def baseEnd_601113 : Nat := 205773264444141250882025

theorem tailTrace_601113 : CollatzResearch.WordTrace tailWord_601113 prefixEnd_601113 205773264444141250882025 := by
  unfold tailWord_601113
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924392271277737772175993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14616261514185158514783995 21924392271277737772175993)
  ·
    refine ⟨16443294203458303329131995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21924392271277737772175993 16443294203458303329131995)
    ·
      refine ⟨24664941305187454993697993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16443294203458303329131995 24664941305187454993697993)
      ·
        refine ⟨18498705978890591245273495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24664941305187454993697993 18498705978890591245273495)
        ·
          refine ⟨27748058968335886867910243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18498705978890591245273495 27748058968335886867910243)
          ·
            refine ⟨41622088452503830301865365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27748058968335886867910243 41622088452503830301865365)
            ·
              refine ⟨1951035396211117045399939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41622088452503830301865365 1951035396211117045399939)
              ·
                refine ⟨2926553094316675568099909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951035396211117045399939 2926553094316675568099909)
                ·
                  refine ⟨548728705184376669018733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2926553094316675568099909 548728705184376669018733)
                  ·
                    refine ⟨205773264444141250882025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548728705184376669018733 205773264444141250882025)
                    ·
                      rfl

theorem cell22_601113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_601113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601113 prefixEnd_601113 := by exact prefixLift 601113
  have htrace : WordTrace (prefixWord ++ tailWord_601113) baseStart_601113 baseEnd_601113 := by
    simpa [prefixWord, tailWord_601113, baseEnd_601113] using wordTrace_append hprefix tailTrace_601113
  have hstable : (prefixWord ++ tailWord_601113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601113).length < 2 ^ (prefixWord ++ tailWord_601113).sum := by decide
  have hdescent : baseEnd_601113 < baseStart_601113 := by decide
  rcases family_descends (prefixWord ++ tailWord_601113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601145 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_601145 : Nat := 118140960795 + 601145 * 2 ^ 59
def prefixEnd_601145 : Nat := 4983230072969 + 3 ^ 40 * 601145 * 2
def baseEnd_601145 : Nat := 205784218698103834081927

theorem tailTrace_601145 : CollatzResearch.WordTrace tailWord_601145 prefixEnd_601145 205784218698103834081927 := by
  unfold tailWord_601145
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925559407161807237340889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14617039604774538158227259 21925559407161807237340889)
  ·
    refine ⟨16444169555371355428005667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21925559407161807237340889 16444169555371355428005667)
    ·
      refine ⟨24666254333057033142008501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16444169555371355428005667 24666254333057033142008501)
      ·
        refine ⟨2312461343724096857063297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24666254333057033142008501 2312461343724096857063297)
        ·
          refine ⟨1734346007793072642797473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312461343724096857063297 1734346007793072642797473)
          ·
            refine ⟨1300759505844804482098105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734346007793072642797473 1300759505844804482098105)
            ·
              refine ⟨975569629383603361573579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300759505844804482098105 975569629383603361573579)
              ·
                refine ⟨1463354444075405042360369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975569629383603361573579 1463354444075405042360369)
                ·
                  refine ⟨1097515833056553781770277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463354444075405042360369 1097515833056553781770277)
                  ·
                    refine ⟨205784218698103834081927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097515833056553781770277 205784218698103834081927)
                    ·
                      rfl

theorem cell22_601145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_601145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601145 prefixEnd_601145 := by exact prefixLift 601145
  have htrace : WordTrace (prefixWord ++ tailWord_601145) baseStart_601145 baseEnd_601145 := by
    simpa [prefixWord, tailWord_601145, baseEnd_601145] using wordTrace_append hprefix tailTrace_601145
  have hstable : (prefixWord ++ tailWord_601145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601145).length < 2 ^ (prefixWord ++ tailWord_601145).sum := by decide
  have hdescent : baseEnd_601145 < baseStart_601145 := by decide
  rcases family_descends (prefixWord ++ tailWord_601145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601209 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 1, 3]
def baseStart_601209 : Nat := 118140960795 + 601209 * 2 ^ 59
def prefixEnd_601209 : Nat := 4983230072969 + 3 ^ 40 * 601209 * 2
def baseEnd_601209 : Nat := 205806127206029000481731

theorem tailTrace_601209 : CollatzResearch.WordTrace tailWord_601209 prefixEnd_601209 205806127206029000481731 := by
  unfold tailWord_601209
  simp only [CollatzResearch.WordTrace]
  refine ⟨21927893678929946167670681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14618595785953297445113787 21927893678929946167670681)
  ·
    refine ⟨16445920259197459625753011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21927893678929946167670681 16445920259197459625753011)
    ·
      refine ⟨24668880388796189438629517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16445920259197459625753011 24668880388796189438629517)
      ·
        refine ⟨9250830145798571039486069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24668880388796189438629517 9250830145798571039486069)
        ·
          refine ⟨867265326168616034951819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9250830145798571039486069 867265326168616034951819)
          ·
            refine ⟨1300897989252924052427729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867265326168616034951819 1300897989252924052427729)
            ·
              refine ⟨975673491939693039320797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300897989252924052427729 975673491939693039320797)
              ·
                refine ⟨365877559477384889745299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975673491939693039320797 365877559477384889745299)
                ·
                  refine ⟨548816339216077334617949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365877559477384889745299 548816339216077334617949)
                  ·
                    refine ⟨205806127206029000481731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548816339216077334617949 205806127206029000481731)
                    ·
                      rfl

theorem cell22_601209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_601209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601209 prefixEnd_601209 := by exact prefixLift 601209
  have htrace : WordTrace (prefixWord ++ tailWord_601209) baseStart_601209 baseEnd_601209 := by
    simpa [prefixWord, tailWord_601209, baseEnd_601209] using wordTrace_append hprefix tailTrace_601209
  have hstable : (prefixWord ++ tailWord_601209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601209).length < 2 ^ (prefixWord ++ tailWord_601209).sum := by decide
  have hdescent : baseEnd_601209 < baseStart_601209 := by decide
  rcases family_descends (prefixWord ++ tailWord_601209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601252 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_601252 : Nat := 118140960795 + 601252 * 2 ^ 59
def prefixEnd_601252 : Nat := 4983230072969 + 3 ^ 40 * 601252 * 2
def baseEnd_601252 : Nat := 205820846984791221656599

theorem tailTrace_601252 : CollatzResearch.WordTrace tailWord_601252 prefixEnd_601252 205820846984791221656599 := by
  unfold tailWord_601252
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964731008887082255743005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14619641345182776340990673 10964731008887082255743005)
  ·
    refine ⟨4111774128332655845903627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10964731008887082255743005 4111774128332655845903627)
    ·
      refine ⟨6167661192498983768855441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111774128332655845903627 6167661192498983768855441)
      ·
        refine ⟨4625745894374237826641581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6167661192498983768855441 4625745894374237826641581)
        ·
          refine ⟨1734654710390339184990593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4625745894374237826641581 1734654710390339184990593)
          ·
            refine ⟨1300991032792754388742945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734654710390339184990593 1300991032792754388742945)
            ·
              refine ⟨975743274594565791557209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300991032792754388742945 975743274594565791557209)
              ·
                refine ⟨731807455945924343667907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975743274594565791557209 731807455945924343667907)
                ·
                  refine ⟨1097711183918886515501861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731807455945924343667907 1097711183918886515501861)
                  ·
                    refine ⟨205820846984791221656599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097711183918886515501861 205820846984791221656599)
                    ·
                      rfl

theorem cell22_601252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_601252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601252 prefixEnd_601252 := by exact prefixLift 601252
  have htrace : WordTrace (prefixWord ++ tailWord_601252) baseStart_601252 baseEnd_601252 := by
    simpa [prefixWord, tailWord_601252, baseEnd_601252] using wordTrace_append hprefix tailTrace_601252
  have hstable : (prefixWord ++ tailWord_601252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601252).length < 2 ^ (prefixWord ++ tailWord_601252).sum := by decide
  have hdescent : baseEnd_601252 < baseStart_601252 := by decide
  rcases family_descends (prefixWord ++ tailWord_601252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601263 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 1, 6]
def baseStart_601263 : Nat := 118140960795 + 601263 * 2 ^ 59
def prefixEnd_601263 : Nat := 4983230072969 + 3 ^ 40 * 601263 * 2
def baseEnd_601263 : Nat := 205824612509590859631565

theorem tailTrace_601263 : CollatzResearch.WordTrace tailWord_601263 prefixEnd_601263 205824612509590859631565 := by
  unfold tailWord_601263
  simp only [CollatzResearch.WordTrace]
  refine ⟨21929863220734313390136443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14619908813822875593424295 21929863220734313390136443)
  ·
    refine ⟨32894794831101470085204665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21929863220734313390136443 32894794831101470085204665)
    ·
      refine ⟨24671096123326102563903499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32894794831101470085204665 24671096123326102563903499)
      ·
        refine ⟨37006644184989153845855249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24671096123326102563903499 37006644184989153845855249)
        ·
          refine ⟨27754983138741865384391437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37006644184989153845855249 27754983138741865384391437)
          ·
            refine ⟨10408118677028199519146789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27754983138741865384391437 10408118677028199519146789)
            ·
              refine ⟨1951522251942787409840023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10408118677028199519146789 1951522251942787409840023)
              ·
                refine ⟨2927283377914181114760035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951522251942787409840023 2927283377914181114760035)
                ·
                  refine ⟨4390925066871271672140053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927283377914181114760035 4390925066871271672140053)
                  ·
                    refine ⟨205824612509590859631565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4390925066871271672140053 205824612509590859631565)
                    ·
                      rfl

theorem cell22_601263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_601263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601263 prefixEnd_601263 := by exact prefixLift 601263
  have htrace : WordTrace (prefixWord ++ tailWord_601263) baseStart_601263 baseEnd_601263 := by
    simpa [prefixWord, tailWord_601263, baseEnd_601263] using wordTrace_append hprefix tailTrace_601263
  have hstable : (prefixWord ++ tailWord_601263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601263).length < 2 ^ (prefixWord ++ tailWord_601263).sum := by decide
  have hdescent : baseEnd_601263 < baseStart_601263 := by decide
  rcases family_descends (prefixWord ++ tailWord_601263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601284 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 6]
def baseStart_601284 : Nat := 118140960795 + 601284 * 2 ^ 59
def prefixEnd_601284 : Nat := 4983230072969 + 3 ^ 40 * 601284 * 2
def baseEnd_601284 : Nat := 68610600412917934952167

theorem tailTrace_601284 : CollatzResearch.WordTrace tailWord_601284 prefixEnd_601284 68610600412917934952167 := by
  unfold tailWord_601284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965314576829116988325453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14620419435772155984433937 10965314576829116988325453)
  ·
    refine ⟨4111992966310918870622045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10965314576829116988325453 4111992966310918870622045)
    ·
      refine ⟨1541997362366594576483267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4111992966310918870622045 1541997362366594576483267)
      ·
        refine ⟨2312996043549891864724901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541997362366594576483267 2312996043549891864724901)
        ·
          refine ⟨433686758165604724635919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2312996043549891864724901 433686758165604724635919)
          ·
            refine ⟨650530137248407086953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433686758165604724635919 650530137248407086953879)
            ·
              refine ⟨975795205872610630430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650530137248407086953879 975795205872610630430819)
              ·
                refine ⟨1463692808808915945646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975795205872610630430819 1463692808808915945646229)
                ·
                  refine ⟨68610600412917934952167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1463692808808915945646229 68610600412917934952167)
                  ·
                    rfl

theorem cell22_601284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_601284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601284 prefixEnd_601284 := by exact prefixLift 601284
  have htrace : WordTrace (prefixWord ++ tailWord_601284) baseStart_601284 baseEnd_601284 := by
    simpa [prefixWord, tailWord_601284, baseEnd_601284] using wordTrace_append hprefix tailTrace_601284
  have hstable : (prefixWord ++ tailWord_601284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601284).length < 2 ^ (prefixWord ++ tailWord_601284).sum := by decide
  have hdescent : baseEnd_601284 < baseStart_601284 := by decide
  rcases family_descends (prefixWord ++ tailWord_601284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601355 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 2, 5]
def baseStart_601355 : Nat := 118140960795 + 601355 * 2 ^ 59
def prefixEnd_601355 : Nat := 4983230072969 + 3 ^ 40 * 601355 * 2
def baseEnd_601355 : Nat := 205856105989733286331283

theorem tailTrace_601355 : CollatzResearch.WordTrace tailWord_601355 prefixEnd_601355 205856105989733286331283 := by
  unfold tailWord_601355
  simp only [CollatzResearch.WordTrace]
  refine ⟨21933218736401013102485519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14622145824267342068323679 21933218736401013102485519)
  ·
    refine ⟨32899828104601519653728279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21933218736401013102485519 32899828104601519653728279)
    ·
      refine ⟨49349742156902279480592419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32899828104601519653728279 49349742156902279480592419)
      ·
        refine ⟨74024613235353419220888629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49349742156902279480592419 74024613235353419220888629)
        ·
          refine ⟨6939807490814383051958309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74024613235353419220888629 6939807490814383051958309)
          ·
            refine ⟨1301213904527696822242183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6939807490814383051958309 1301213904527696822242183)
            ·
              refine ⟨1951820856791545233363275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301213904527696822242183 1951820856791545233363275)
              ·
                refine ⟨2927731285187317850044913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951820856791545233363275 2927731285187317850044913)
                ·
                  refine ⟨2195798463890488387533685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2927731285187317850044913 2195798463890488387533685)
                  ·
                    refine ⟨205856105989733286331283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2195798463890488387533685 205856105989733286331283)
                    ·
                      rfl

theorem cell22_601355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_601355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601355 prefixEnd_601355 := by exact prefixLift 601355
  have htrace : WordTrace (prefixWord ++ tailWord_601355) baseStart_601355 baseEnd_601355 := by
    simpa [prefixWord, tailWord_601355, baseEnd_601355] using wordTrace_append hprefix tailTrace_601355
  have hstable : (prefixWord ++ tailWord_601355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601355).length < 2 ^ (prefixWord ++ tailWord_601355).sum := by decide
  have hdescent : baseEnd_601355 < baseStart_601355 := by decide
  rcases family_descends (prefixWord ++ tailWord_601355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601402 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_601402 : Nat := 118140960795 + 601402 * 2 ^ 59
def prefixEnd_601402 : Nat := 4983230072969 + 3 ^ 40 * 601402 * 2
def baseEnd_601402 : Nat := 68624065016746943468713

theorem tailTrace_601402 : CollatzResearch.WordTrace tailWord_601402 prefixEnd_601402 68624065016746943468713 := by
  unfold tailWord_601402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483733241807685032361615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14623288644820493419630973 5483733241807685032361615)
  ·
    refine ⟨8225599862711527548542423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5483733241807685032361615 8225599862711527548542423)
    ·
      refine ⟨12338399794067291322813635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8225599862711527548542423 12338399794067291322813635)
      ·
        refine ⟨18507599691100936984220453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12338399794067291322813635 18507599691100936984220453)
        ·
          refine ⟨3470174942081425684541335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18507599691100936984220453 3470174942081425684541335)
          ·
            refine ⟨5205262413122138526812003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470174942081425684541335 5205262413122138526812003)
            ·
              refine ⟨7807893619683207790218005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205262413122138526812003 7807893619683207790218005)
              ·
                refine ⟨365995013422650365166469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7807893619683207790218005 365995013422650365166469)
                ·
                  refine ⟨68624065016746943468713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365995013422650365166469 68624065016746943468713)
                  ·
                    rfl

theorem cell22_601402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_601402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601402 prefixEnd_601402 := by exact prefixLift 601402
  have htrace : WordTrace (prefixWord ++ tailWord_601402) baseStart_601402 baseEnd_601402 := by
    simpa [prefixWord, tailWord_601402, baseEnd_601402] using wordTrace_append hprefix tailTrace_601402
  have hstable : (prefixWord ++ tailWord_601402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601402).length < 2 ^ (prefixWord ++ tailWord_601402).sum := by decide
  have hdescent : baseEnd_601402 < baseStart_601402 := by decide
  rcases family_descends (prefixWord ++ tailWord_601402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601415 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_601415 : Nat := 118140960795 + 601415 * 2 ^ 59
def prefixEnd_601415 : Nat := 4983230072969 + 3 ^ 40 * 601415 * 2
def baseEnd_601415 : Nat := 205876645215913129831099

theorem tailTrace_601415 : CollatzResearch.WordTrace tailWord_601415 prefixEnd_601415 205876645215913129831099 := by
  unfold tailWord_601415
  simp only [CollatzResearch.WordTrace]
  refine ⟨21935407116183643349669699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14623604744122428899779799 21935407116183643349669699)
  ·
    refine ⟨32903110674275465024504549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21935407116183643349669699 32903110674275465024504549)
    ·
      refine ⟨6169333251426649692094603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32903110674275465024504549 6169333251426649692094603)
      ·
        refine ⟨9253999877139974538141905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6169333251426649692094603 9253999877139974538141905)
        ·
          refine ⟨6940499907854980903606429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9253999877139974538141905 6940499907854980903606429)
          ·
            refine ⟨2602687465445617838852411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6940499907854980903606429 2602687465445617838852411)
            ·
              refine ⟨3904031198168426758278617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602687465445617838852411 3904031198168426758278617)
              ·
                refine ⟨2928023398626320068708963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904031198168426758278617 2928023398626320068708963)
                ·
                  refine ⟨4392035097939480103063445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928023398626320068708963 4392035097939480103063445)
                  ·
                    refine ⟨205876645215913129831099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4392035097939480103063445 205876645215913129831099)
                    ·
                      rfl

theorem cell22_601415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_601415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601415 prefixEnd_601415 := by exact prefixLift 601415
  have htrace : WordTrace (prefixWord ++ tailWord_601415) baseStart_601415 baseEnd_601415 := by
    simpa [prefixWord, tailWord_601415, baseEnd_601415] using wordTrace_append hprefix tailTrace_601415
  have hstable : (prefixWord ++ tailWord_601415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601415).length < 2 ^ (prefixWord ++ tailWord_601415).sum := by decide
  have hdescent : baseEnd_601415 < baseStart_601415 := by decide
  rcases family_descends (prefixWord ++ tailWord_601415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601417 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_601417 : Nat := 118140960795 + 601417 * 2 ^ 59
def prefixEnd_601417 : Nat := 4983230072969 + 3 ^ 40 * 601417 * 2
def baseEnd_601417 : Nat := 205877329856785791281093

theorem tailTrace_601417 : CollatzResearch.WordTrace tailWord_601417 prefixEnd_601417 205877329856785791281093 := by
  unfold tailWord_601417
  simp only [CollatzResearch.WordTrace]
  refine ⟨21935480062176397691242505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14623653374784265127495003 21935480062176397691242505)
  ·
    refine ⟨16451610046632298268431879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21935480062176397691242505 16451610046632298268431879)
    ·
      refine ⟨24677415069948447402647819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16451610046632298268431879 24677415069948447402647819)
      ·
        refine ⟨37016122604922671103971729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24677415069948447402647819 37016122604922671103971729)
        ·
          refine ⟨27762091953692003327978797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37016122604922671103971729 27762091953692003327978797)
          ·
            refine ⟨10410784482634501247992049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27762091953692003327978797 10410784482634501247992049)
            ·
              refine ⟨7808088361975875935994037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10410784482634501247992049 7808088361975875935994037)
              ·
                refine ⟨732008283935238368999441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7808088361975875935994037 732008283935238368999441)
                ·
                  refine ⟨549006212951428776749581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732008283935238368999441 549006212951428776749581)
                  ·
                    refine ⟨205877329856785791281093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549006212951428776749581 205877329856785791281093)
                    ·
                      rfl

theorem cell22_601417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_601417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601417 prefixEnd_601417 := by exact prefixLift 601417
  have htrace : WordTrace (prefixWord ++ tailWord_601417) baseStart_601417 baseEnd_601417 := by
    simpa [prefixWord, tailWord_601417, baseEnd_601417] using wordTrace_append hprefix tailTrace_601417
  have hstable : (prefixWord ++ tailWord_601417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601417).length < 2 ^ (prefixWord ++ tailWord_601417).sum := by decide
  have hdescent : baseEnd_601417 < baseStart_601417 := by decide
  rcases family_descends (prefixWord ++ tailWord_601417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601447 : List Nat := [1, 1, 5, 1, 4, 2, 8]
def baseStart_601447 : Nat := 118140960795 + 601447 * 2 ^ 59
def prefixEnd_601447 : Nat := 4983230072969 + 3 ^ 40 * 601447 * 2
def baseEnd_601447 : Nat := 7625466647032433815963

theorem tailTrace_601447 : CollatzResearch.WordTrace tailWord_601447 prefixEnd_601447 7625466647032433815963 := by
  unfold tailWord_601447
  simp only [CollatzResearch.WordTrace]
  refine ⟨21936574252067712814834595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14624382834711808543223063 21936574252067712814834595)
  ·
    refine ⟨32904861378101569222251893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21936574252067712814834595 32904861378101569222251893)
    ·
      refine ⟨3084830754197022114586115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32904861378101569222251893 3084830754197022114586115)
      ·
        refine ⟨4627246131295533171879173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084830754197022114586115 4627246131295533171879173)
        ·
          refine ⟨867608649617912469727345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4627246131295533171879173 867608649617912469727345)
          ·
            refine ⟨650706487213434352295509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867608649617912469727345 650706487213434352295509)
            ·
              refine ⟨7625466647032433815963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 650706487213434352295509 7625466647032433815963)
              ·
                rfl

theorem cell22_601447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 8].length) (baseStart_601447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601447 prefixEnd_601447 := by exact prefixLift 601447
  have htrace : WordTrace (prefixWord ++ tailWord_601447) baseStart_601447 baseEnd_601447 := by
    simpa [prefixWord, tailWord_601447, baseEnd_601447] using wordTrace_append hprefix tailTrace_601447
  have hstable : (prefixWord ++ tailWord_601447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601447).length < 2 ^ (prefixWord ++ tailWord_601447).sum := by decide
  have hdescent : baseEnd_601447 < baseStart_601447 := by decide
  rcases family_descends (prefixWord ++ tailWord_601447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601552 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_601552 : Nat := 118140960795 + 601552 * 2 ^ 59
def prefixEnd_601552 : Nat := 4983230072969 + 3 ^ 40 * 601552 * 2
def baseEnd_601552 : Nat := 205923543115690439155679

theorem tailTrace_601552 : CollatzResearch.WordTrace tailWord_601552 prefixEnd_601552 205923543115690439155679 := by
  unfold tailWord_601552
  simp only [CollatzResearch.WordTrace]
  refine ⟨10970201958343657873703455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14626935944458210498271273 10970201958343657873703455)
  ·
    refine ⟨16455302937515486810555183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10970201958343657873703455 16455302937515486810555183)
    ·
      refine ⟨24682954406273230215832775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16455302937515486810555183 24682954406273230215832775)
      ·
        refine ⟨37024431609409845323749163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24682954406273230215832775 37024431609409845323749163)
        ·
          refine ⟨55536647414114767985623745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37024431609409845323749163 55536647414114767985623745)
          ·
            refine ⟨41652485560586075989217809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55536647414114767985623745 41652485560586075989217809)
            ·
              refine ⟨31239364170439556991913357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41652485560586075989217809 31239364170439556991913357)
              ·
                refine ⟨11714761563914833871967509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31239364170439556991913357 11714761563914833871967509)
                ·
                  refine ⟨549129448308507837748477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11714761563914833871967509 549129448308507837748477)
                  ·
                    refine ⟨205923543115690439155679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549129448308507837748477 205923543115690439155679)
                    ·
                      rfl

theorem cell22_601552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_601552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601552 prefixEnd_601552 := by exact prefixLift 601552
  have htrace : WordTrace (prefixWord ++ tailWord_601552) baseStart_601552 baseEnd_601552 := by
    simpa [prefixWord, tailWord_601552, baseEnd_601552] using wordTrace_append hprefix tailTrace_601552
  have hstable : (prefixWord ++ tailWord_601552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601552).length < 2 ^ (prefixWord ++ tailWord_601552).sum := by decide
  have hdescent : baseEnd_601552 < baseStart_601552 := by decide
  rcases family_descends (prefixWord ++ tailWord_601552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601556 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_601556 : Nat := 118140960795 + 601556 * 2 ^ 59
def prefixEnd_601556 : Nat := 4983230072969 + 3 ^ 40 * 601556 * 2
def baseEnd_601556 : Nat := 205924912397435762055667

theorem tailTrace_601556 : CollatzResearch.WordTrace tailWord_601556 prefixEnd_601556 205924912397435762055667 := by
  unfold tailWord_601556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10970274904336412215276261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14627033205781882953701681 10970274904336412215276261)
  ·
    refine ⟨2056926544563077290364299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10970274904336412215276261 2056926544563077290364299)
    ·
      refine ⟨3085389816844615935546449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2056926544563077290364299 3085389816844615935546449)
      ·
        refine ⟨2314042362633461951659837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085389816844615935546449 2314042362633461951659837)
        ·
          refine ⟨867765885987548231872439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2314042362633461951659837 867765885987548231872439)
          ·
            refine ⟨1301648828981322347808659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867765885987548231872439 1301648828981322347808659)
            ·
              refine ⟨1952473243471983521712989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301648828981322347808659 1952473243471983521712989)
              ·
                refine ⟨732177466301993820642371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1952473243471983521712989 732177466301993820642371)
                ·
                  refine ⟨1098266199452990730963557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732177466301993820642371 1098266199452990730963557)
                  ·
                    refine ⟨205924912397435762055667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1098266199452990730963557 205924912397435762055667)
                    ·
                      rfl

theorem cell22_601556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_601556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601556 prefixEnd_601556 := by exact prefixLift 601556
  have htrace : WordTrace (prefixWord ++ tailWord_601556) baseStart_601556 baseEnd_601556 := by
    simpa [prefixWord, tailWord_601556, baseEnd_601556] using wordTrace_append hprefix tailTrace_601556
  have hstable : (prefixWord ++ tailWord_601556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601556).length < 2 ^ (prefixWord ++ tailWord_601556).sum := by decide
  have hdescent : baseEnd_601556 < baseStart_601556 := by decide
  rcases family_descends (prefixWord ++ tailWord_601556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601567 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 4, 4]
def baseStart_601567 : Nat := 118140960795 + 601567 * 2 ^ 59
def prefixEnd_601567 : Nat := 4983230072969 + 3 ^ 40 * 601567 * 2
def baseEnd_601567 : Nat := 205928677922235400030633

theorem tailTrace_601567 : CollatzResearch.WordTrace tailWord_601567 prefixEnd_601567 205928677922235400030633 := by
  unfold tailWord_601567
  simp only [CollatzResearch.WordTrace]
  refine ⟨21940951011632973309202955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14627300674421982206135303 21940951011632973309202955)
  ·
    refine ⟨32911426517449459963804433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21940951011632973309202955 32911426517449459963804433)
    ·
      refine ⟨24683569888087094972853325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32911426517449459963804433 24683569888087094972853325)
      ·
        refine ⟨9256338708032660614819997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24683569888087094972853325 9256338708032660614819997)
        ·
          refine ⟨3471127015512247730557499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9256338708032660614819997 3471127015512247730557499)
          ·
            refine ⟨5206690523268371595836249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471127015512247730557499 5206690523268371595836249)
            ·
              refine ⟨3905017892451278696877187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5206690523268371595836249 3905017892451278696877187)
              ·
                refine ⟨5857526838676918045315781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905017892451278696877187 5857526838676918045315781)
                ·
                  refine ⟨1098286282251922133496709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5857526838676918045315781 1098286282251922133496709)
                  ·
                    refine ⟨205928677922235400030633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1098286282251922133496709 205928677922235400030633)
                    ·
                      rfl

theorem cell22_601567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_601567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601567 prefixEnd_601567 := by exact prefixLift 601567
  have htrace : WordTrace (prefixWord ++ tailWord_601567) baseStart_601567 baseEnd_601567 := by
    simpa [prefixWord, tailWord_601567, baseEnd_601567] using wordTrace_append hprefix tailTrace_601567
  have hstable : (prefixWord ++ tailWord_601567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601567).length < 2 ^ (prefixWord ++ tailWord_601567).sum := by decide
  have hdescent : baseEnd_601567 < baseStart_601567 := by decide
  rcases family_descends (prefixWord ++ tailWord_601567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601569 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_601569 : Nat := 118140960795 + 601569 * 2 ^ 59
def prefixEnd_601569 : Nat := 4983230072969 + 3 ^ 40 * 601569 * 2
def baseEnd_601569 : Nat := 205929362563108061480627

theorem tailTrace_601569 : CollatzResearch.WordTrace tailWord_601569 prefixEnd_601569 205929362563108061480627 := by
  unfold tailWord_601569
  simp only [CollatzResearch.WordTrace]
  refine ⟨21941023957625727650775761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14627349305083818433850507 21941023957625727650775761)
  ·
    refine ⟨16455767968219295738081821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21941023957625727650775761 16455767968219295738081821)
    ·
      refine ⟨6170912988082235901780683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16455767968219295738081821 6170912988082235901780683)
      ·
        refine ⟨9256369482123353852671025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170912988082235901780683 9256369482123353852671025)
        ·
          refine ⟨6942277111592515389503269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9256369482123353852671025 6942277111592515389503269)
          ·
            refine ⟨1301676958423596635531863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6942277111592515389503269 1301676958423596635531863)
            ·
              refine ⟨1952515437635394953297795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301676958423596635531863 1952515437635394953297795)
              ·
                refine ⟨2928773156453092429946693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952515437635394953297795 2928773156453092429946693)
                ·
                  refine ⟨549144966834954830615005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2928773156453092429946693 549144966834954830615005)
                  ·
                    refine ⟨205929362563108061480627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549144966834954830615005 205929362563108061480627)
                    ·
                      rfl

theorem cell22_601569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_601569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601569 prefixEnd_601569 := by exact prefixLift 601569
  have htrace : WordTrace (prefixWord ++ tailWord_601569) baseStart_601569 baseEnd_601569 := by
    simpa [prefixWord, tailWord_601569, baseEnd_601569] using wordTrace_append hprefix tailTrace_601569
  have hstable : (prefixWord ++ tailWord_601569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601569).length < 2 ^ (prefixWord ++ tailWord_601569).sum := by decide
  have hdescent : baseEnd_601569 < baseStart_601569 := by decide
  rcases family_descends (prefixWord ++ tailWord_601569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601582 : List Nat := [4, 1, 2, 1, 2, 1, 2, 9]
def baseStart_601582 : Nat := 118140960795 + 601582 * 2 ^ 59
def prefixEnd_601582 : Nat := 4983230072969 + 3 ^ 40 * 601582 * 2
def baseEnd_601582 : Nat := 22881534747642262322843

theorem tailTrace_601582 : CollatzResearch.WordTrace tailWord_601582 prefixEnd_601582 22881534747642262322843 := by
  unfold tailWord_601582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742687263322328858874875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14627665404385753913999333 2742687263322328858874875)
  ·
    refine ⟨4114030894983493288312313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2742687263322328858874875 4114030894983493288312313)
    ·
      refine ⟨3085523171237619966234235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4114030894983493288312313 3085523171237619966234235)
      ·
        refine ⟨4628284756856429949351353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3085523171237619966234235 4628284756856429949351353)
        ·
          refine ⟨3471213567642322462013515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4628284756856429949351353 3471213567642322462013515)
          ·
            refine ⟨5206820351463483693020273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471213567642322462013515 5206820351463483693020273)
            ·
              refine ⟨3905115263597612769765205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5206820351463483693020273 3905115263597612769765205)
              ·
                refine ⟨22881534747642262322843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3905115263597612769765205 22881534747642262322843)
                ·
                  rfl

theorem cell22_601582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_601582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601582 prefixEnd_601582 := by exact prefixLift 601582
  have htrace : WordTrace (prefixWord ++ tailWord_601582) baseStart_601582 baseEnd_601582 := by
    simpa [prefixWord, tailWord_601582, baseEnd_601582] using wordTrace_append hprefix tailTrace_601582
  have hstable : (prefixWord ++ tailWord_601582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601582).length < 2 ^ (prefixWord ++ tailWord_601582).sum := by decide
  have hdescent : baseEnd_601582 < baseStart_601582 := by decide
  rcases family_descends (prefixWord ++ tailWord_601582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601586 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_601586 : Nat := 118140960795 + 601586 * 2 ^ 59
def prefixEnd_601586 : Nat := 4983230072969 + 3 ^ 40 * 601586 * 2
def baseEnd_601586 : Nat := 205935182010525683805575

theorem tailTrace_601586 : CollatzResearch.WordTrace tailWord_601586 prefixEnd_601586 205935182010525683805575 := by
  unfold tailWord_601586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5485410999641034888536153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14627762665709426369429741 5485410999641034888536153)
  ·
    refine ⟨4114058249730776166402115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5485410999641034888536153 4114058249730776166402115)
    ·
      refine ⟨6171087374596164249603173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4114058249730776166402115 6171087374596164249603173)
      ·
        refine ⟨1157078882736780796800595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6171087374596164249603173 1157078882736780796800595)
        ·
          refine ⟨1735618324105171195200893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157078882736780796800595 1735618324105171195200893)
          ·
            refine ⟨650856871539439198200335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1735618324105171195200893 650856871539439198200335)
            ·
              refine ⟨976285307309158797300503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650856871539439198200335 976285307309158797300503)
              ·
                refine ⟨1464427960963738195950755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976285307309158797300503 1464427960963738195950755)
                ·
                  refine ⟨2196641941445607293926133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464427960963738195950755 2196641941445607293926133)
                  ·
                    refine ⟨205935182010525683805575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2196641941445607293926133 205935182010525683805575)
                    ·
                      rfl

theorem cell22_601586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_601586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601586 prefixEnd_601586 := by exact prefixLift 601586
  have htrace : WordTrace (prefixWord ++ tailWord_601586) baseStart_601586 baseEnd_601586 := by
    simpa [prefixWord, tailWord_601586, baseEnd_601586] using wordTrace_append hprefix tailTrace_601586
  have hstable : (prefixWord ++ tailWord_601586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601586).length < 2 ^ (prefixWord ++ tailWord_601586).sum := by decide
  have hdescent : baseEnd_601586 < baseStart_601586 := by decide
  rcases family_descends (prefixWord ++ tailWord_601586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601631 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 1, 3]
def baseStart_601631 : Nat := 118140960795 + 601631 * 2 ^ 59
def prefixEnd_601631 : Nat := 4983230072969 + 3 ^ 40 * 601631 * 2
def baseEnd_601631 : Nat := 205950586430160566430437

theorem tailTrace_601631 : CollatzResearch.WordTrace tailWord_601631 prefixEnd_601631 205950586430160566430437 := by
  unfold tailWord_601631
  simp only [CollatzResearch.WordTrace]
  refine ⟨21943285283401112239532747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14628856855600741493021831 21943285283401112239532747)
  ·
    refine ⟨32914927925101668359299121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21943285283401112239532747 32914927925101668359299121)
    ·
      refine ⟨24686195943826251269474341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32914927925101668359299121 24686195943826251269474341)
      ·
        refine ⟨4628661739467422113026439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24686195943826251269474341 4628661739467422113026439)
        ·
          refine ⟨6942992609201133169539659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628661739467422113026439 6942992609201133169539659)
          ·
            refine ⟨10414488913801699754309489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6942992609201133169539659 10414488913801699754309489)
            ·
              refine ⟨7810866685351274815732117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10414488913801699754309489 7810866685351274815732117)
              ·
                refine ⟨366134375875841006987443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7810866685351274815732117 366134375875841006987443)
                ·
                  refine ⟨549201563813761510481165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366134375875841006987443 549201563813761510481165)
                  ·
                    refine ⟨205950586430160566430437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549201563813761510481165 205950586430160566430437)
                    ·
                      rfl

theorem cell22_601631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_601631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601631 prefixEnd_601631 := by exact prefixLift 601631
  have htrace : WordTrace (prefixWord ++ tailWord_601631) baseStart_601631 baseEnd_601631 := by
    simpa [prefixWord, tailWord_601631, baseEnd_601631] using wordTrace_append hprefix tailTrace_601631
  have hstable : (prefixWord ++ tailWord_601631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601631).length < 2 ^ (prefixWord ++ tailWord_601631).sum := by decide
  have hdescent : baseEnd_601631 < baseStart_601631 := by decide
  rcases family_descends (prefixWord ++ tailWord_601631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601693 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_601693 : Nat := 118140960795 + 601693 * 2 ^ 59
def prefixEnd_601693 : Nat := 4983230072969 + 3 ^ 40 * 601693 * 2
def baseEnd_601693 : Nat := 205971810297213071380247

theorem tailTrace_601693 : CollatzResearch.WordTrace tailWord_601693 prefixEnd_601693 205971810297213071380247 := by
  unfold tailWord_601693
  simp only [CollatzResearch.WordTrace]
  refine ⟨21945546609176496828289733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14630364406117664552193155 21945546609176496828289733)
  ·
    refine ⟨4114789989220593155304325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21945546609176496828289733 4114789989220593155304325)
    ·
      refine ⟨771523122978861216619561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4114789989220593155304325 771523122978861216619561)
      ·
        refine ⟨578642342234145912464671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771523122978861216619561 578642342234145912464671)
        ·
          refine ⟨867963513351218868697007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578642342234145912464671 867963513351218868697007)
          ·
            refine ⟨1301945270026828303045511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867963513351218868697007 1301945270026828303045511)
            ·
              refine ⟨1952917905040242454568267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301945270026828303045511 1952917905040242454568267)
              ·
                refine ⟨2929376857560363681852401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952917905040242454568267 2929376857560363681852401)
                ·
                  refine ⟨2197032643170272761389301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929376857560363681852401 2197032643170272761389301)
                  ·
                    refine ⟨205971810297213071380247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2197032643170272761389301 205971810297213071380247)
                    ·
                      rfl

theorem cell22_601693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_601693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601693 prefixEnd_601693 := by exact prefixLift 601693
  have htrace : WordTrace (prefixWord ++ tailWord_601693) baseStart_601693 baseEnd_601693 := by
    simpa [prefixWord, tailWord_601693, baseEnd_601693] using wordTrace_append hprefix tailTrace_601693
  have hstable : (prefixWord ++ tailWord_601693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601693).length < 2 ^ (prefixWord ++ tailWord_601693).sum := by decide
  have hdescent : baseEnd_601693 < baseStart_601693 := by decide
  rcases family_descends (prefixWord ++ tailWord_601693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601738 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_601738 : Nat := 118140960795 + 601738 * 2 ^ 59
def prefixEnd_601738 : Nat := 4983230072969 + 3 ^ 40 * 601738 * 2
def baseEnd_601738 : Nat := 205987214716847954005109

theorem tailTrace_601738 : CollatzResearch.WordTrace tailWord_601738 prefixEnd_601738 205987214716847954005109 := by
  unfold tailWord_601738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486796973503367378419467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14631458596008979675785245 5486796973503367378419467)
  ·
    refine ⟨8230195460255051067629201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5486796973503367378419467 8230195460255051067629201)
    ·
      refine ⟨6172646595191288300721901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8230195460255051067629201 6172646595191288300721901)
      ·
        refine ⟨2314742473196733112770713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6172646595191288300721901 2314742473196733112770713)
        ·
          refine ⟨1736056854897549834578035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2314742473196733112770713 1736056854897549834578035)
          ·
            refine ⟨2604085282346324751867053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736056854897549834578035 2604085282346324751867053)
            ·
              refine ⟨976531980879871781950145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2604085282346324751867053 976531980879871781950145)
              ·
                refine ⟨732398985659903836462609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976531980879871781950145 732398985659903836462609)
                ·
                  refine ⟨549299239244927877346957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732398985659903836462609 549299239244927877346957)
                  ·
                    refine ⟨205987214716847954005109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549299239244927877346957 205987214716847954005109)
                    ·
                      rfl

theorem cell22_601738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_601738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601738 prefixEnd_601738 := by exact prefixLift 601738
  have htrace : WordTrace (prefixWord ++ tailWord_601738) baseStart_601738 baseEnd_601738 := by
    simpa [prefixWord, tailWord_601738, baseEnd_601738] using wordTrace_append hprefix tailTrace_601738
  have hstable : (prefixWord ++ tailWord_601738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601738).length < 2 ^ (prefixWord ++ tailWord_601738).sum := by decide
  have hdescent : baseEnd_601738 < baseStart_601738 := by decide
  rcases family_descends (prefixWord ++ tailWord_601738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601796 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_601796 : Nat := 118140960795 + 601796 * 2 ^ 59
def prefixEnd_601796 : Nat := 4983230072969 + 3 ^ 40 * 601796 * 2
def baseEnd_601796 : Nat := 68669023100718378684977

theorem tailTrace_601796 : CollatzResearch.WordTrace tailWord_601796 prefixEnd_601796 68669023100718378684977 := by
  unfold tailWord_601796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974651663901672709644621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14632868885202230279526161 10974651663901672709644621)
  ·
    refine ⟨4115494373963127266116733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10974651663901672709644621 4115494373963127266116733)
    ·
      refine ⟨1543310390236172724793775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4115494373963127266116733 1543310390236172724793775)
      ·
        refine ⟨2314965585354259087190663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543310390236172724793775 2314965585354259087190663)
        ·
          refine ⟨3472448378031388630785995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314965585354259087190663 3472448378031388630785995)
          ·
            refine ⟨5208672567047082946178993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472448378031388630785995 5208672567047082946178993)
            ·
              refine ⟨3906504425285312209634245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5208672567047082946178993 3906504425285312209634245)
              ·
                refine ⟨732469579740996039306421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3906504425285312209634245 732469579740996039306421)
                ·
                  refine ⟨68669023100718378684977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732469579740996039306421 68669023100718378684977)
                  ·
                    rfl

theorem cell22_601796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_601796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601796 prefixEnd_601796 := by exact prefixLift 601796
  have htrace : WordTrace (prefixWord ++ tailWord_601796) baseStart_601796 baseEnd_601796 := by
    simpa [prefixWord, tailWord_601796, baseEnd_601796] using wordTrace_append hprefix tailTrace_601796
  have hstable : (prefixWord ++ tailWord_601796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601796).length < 2 ^ (prefixWord ++ tailWord_601796).sum := by decide
  have hdescent : baseEnd_601796 < baseStart_601796 := by decide
  rcases family_descends (prefixWord ++ tailWord_601796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601800 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 1, 3]
def baseStart_601800 : Nat := 118140960795 + 601800 * 2 ^ 59
def prefixEnd_601800 : Nat := 4983230072969 + 3 ^ 40 * 601800 * 2
def baseEnd_601800 : Nat := 206008438583900458954919

theorem tailTrace_601800 : CollatzResearch.WordTrace tailWord_601800 prefixEnd_601800 206008438583900458954919 := by
  unfold tailWord_601800
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974724609894427051217427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14632966146525902734956569 10974724609894427051217427)
  ·
    refine ⟨16462086914841640576826141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10974724609894427051217427 16462086914841640576826141)
    ·
      refine ⟨6173282593065615216309803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16462086914841640576826141 6173282593065615216309803)
      ·
        refine ⟨9259923889598422824464705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6173282593065615216309803 9259923889598422824464705)
        ·
          refine ⟨6944942917198817118348529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9259923889598422824464705 6944942917198817118348529)
          ·
            refine ⟨5208707187899112838761397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6944942917198817118348529 5208707187899112838761397)
            ·
              refine ⟨488316298865541828633881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5208707187899112838761397 488316298865541828633881)
              ·
                refine ⟨366237224149156371475411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488316298865541828633881 366237224149156371475411)
                ·
                  refine ⟨549355836223734557213117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366237224149156371475411 549355836223734557213117)
                  ·
                    refine ⟨206008438583900458954919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549355836223734557213117 206008438583900458954919)
                    ·
                      rfl

theorem cell22_601800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_601800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601800 prefixEnd_601800 := by exact prefixLift 601800
  have htrace : WordTrace (prefixWord ++ tailWord_601800) baseStart_601800 baseEnd_601800 := by
    simpa [prefixWord, tailWord_601800, baseEnd_601800] using wordTrace_append hprefix tailTrace_601800
  have hstable : (prefixWord ++ tailWord_601800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601800).length < 2 ^ (prefixWord ++ tailWord_601800).sum := by decide
  have hdescent : baseEnd_601800 < baseStart_601800 := by decide
  rcases family_descends (prefixWord ++ tailWord_601800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601824 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_601824 : Nat := 118140960795 + 601824 * 2 ^ 59
def prefixEnd_601824 : Nat := 4983230072969 + 3 ^ 40 * 601824 * 2
def baseEnd_601824 : Nat := 68672218091457465451615

theorem tailTrace_601824 : CollatzResearch.WordTrace tailWord_601824 prefixEnd_601824 68672218091457465451615 := by
  unfold tailWord_601824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10975162285850953100654263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14633549714467937467539017 10975162285850953100654263)
  ·
    refine ⟨16462743428776429650981395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10975162285850953100654263 16462743428776429650981395)
    ·
      refine ⟨24694115143164644476472093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16462743428776429650981395 24694115143164644476472093)
      ·
        refine ⟨9260293178686741678677035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24694115143164644476472093 9260293178686741678677035)
        ·
          refine ⟨13890439768030112518015553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9260293178686741678677035 13890439768030112518015553)
          ·
            refine ⟨10417829826022584388511665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13890439768030112518015553 10417829826022584388511665)
            ·
              refine ⟨7813372369516938291383749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10417829826022584388511665 7813372369516938291383749)
              ·
                refine ⟨1465007319284425929634453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7813372369516938291383749 1465007319284425929634453)
                ·
                  refine ⟨68672218091457465451615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1465007319284425929634453 68672218091457465451615)
                  ·
                    rfl

theorem cell22_601824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_601824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601824 prefixEnd_601824 := by exact prefixLift 601824
  have htrace : WordTrace (prefixWord ++ tailWord_601824) baseStart_601824 baseEnd_601824 := by
    simpa [prefixWord, tailWord_601824, baseEnd_601824] using wordTrace_append hprefix tailTrace_601824
  have hstable : (prefixWord ++ tailWord_601824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601824).length < 2 ^ (prefixWord ++ tailWord_601824).sum := by decide
  have hdescent : baseEnd_601824 < baseStart_601824 := by decide
  rcases family_descends (prefixWord ++ tailWord_601824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601907 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 2, 3]
def baseStart_601907 : Nat := 118140960795 + 601907 * 2 ^ 59
def prefixEnd_601907 : Nat := 4983230072969 + 3 ^ 40 * 601907 * 2
def baseEnd_601907 : Nat := 206045066870587846529591

theorem tailTrace_601907 : CollatzResearch.WordTrace tailWord_601907 prefixEnd_601907 206045066870587846529591 := by
  unfold tailWord_601907
  simp only [CollatzResearch.WordTrace]
  refine ⟨21953351830401211376579975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14635567886934140917719983 21953351830401211376579975)
  ·
    refine ⟨32930027745601817064869963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21953351830401211376579975 32930027745601817064869963)
    ·
      refine ⟨49395041618402725597304945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32930027745601817064869963 49395041618402725597304945)
      ·
        refine ⟨37046281213802044197978709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49395041618402725597304945 37046281213802044197978709)
        ·
          refine ⟨434136107974242705445063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 37046281213802044197978709 434136107974242705445063)
          ·
            refine ⟨651204161961364058167595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434136107974242705445063 651204161961364058167595)
            ·
              refine ⟨976806242942046087251393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651204161961364058167595 976806242942046087251393)
              ·
                refine ⟨732604682206534565438545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976806242942046087251393 732604682206534565438545)
                ·
                  refine ⟨549453511654900924078909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732604682206534565438545 549453511654900924078909)
                  ·
                    refine ⟨206045066870587846529591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549453511654900924078909 206045066870587846529591)
                    ·
                      rfl

theorem cell22_601907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 3].length) (baseStart_601907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601907 prefixEnd_601907 := by exact prefixLift 601907
  have htrace : WordTrace (prefixWord ++ tailWord_601907) baseStart_601907 baseEnd_601907 := by
    simpa [prefixWord, tailWord_601907, baseEnd_601907] using wordTrace_append hprefix tailTrace_601907
  have hstable : (prefixWord ++ tailWord_601907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601907).length < 2 ^ (prefixWord ++ tailWord_601907).sum := by decide
  have hdescent : baseEnd_601907 < baseStart_601907 := by decide
  rcases family_descends (prefixWord ++ tailWord_601907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601952 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 1, 3]
def baseStart_601952 : Nat := 118140960795 + 601952 * 2 ^ 59
def prefixEnd_601952 : Nat := 4983230072969 + 3 ^ 40 * 601952 * 2
def baseEnd_601952 : Nat := 206060471290222729154453

theorem tailTrace_601952 : CollatzResearch.WordTrace tailWord_601952 prefixEnd_601952 206060471290222729154453 := by
  unfold tailWord_601952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977496557619092030984055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14636662076825456041312073 10977496557619092030984055)
  ·
    refine ⟨16466244836428638046476083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10977496557619092030984055 16466244836428638046476083)
    ·
      refine ⟨24699367254642957069714125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16466244836428638046476083 24699367254642957069714125)
      ·
        refine ⟨9262262720491108901142797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24699367254642957069714125 9262262720491108901142797)
        ·
          refine ⟨3473348520184165837928549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9262262720491108901142797 3473348520184165837928549)
          ·
            refine ⟨651252847534531094611603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3473348520184165837928549 651252847534531094611603)
            ·
              refine ⟨976879271301796641917405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651252847534531094611603 976879271301796641917405)
              ·
                refine ⟨366329726738173740719027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 976879271301796641917405 366329726738173740719027)
                ·
                  refine ⟨549494590107260611078541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366329726738173740719027 549494590107260611078541)
                  ·
                    refine ⟨206060471290222729154453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549494590107260611078541 206060471290222729154453)
                    ·
                      rfl

theorem cell22_601952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_601952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601952 prefixEnd_601952 := by exact prefixLift 601952
  have htrace : WordTrace (prefixWord ++ tailWord_601952) baseStart_601952 baseEnd_601952 := by
    simpa [prefixWord, tailWord_601952, baseEnd_601952] using wordTrace_append hprefix tailTrace_601952
  have hstable : (prefixWord ++ tailWord_601952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601952).length < 2 ^ (prefixWord ++ tailWord_601952).sum := by decide
  have hdescent : baseEnd_601952 < baseStart_601952 := by decide
  rcases family_descends (prefixWord ++ tailWord_601952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601982 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_601982 : Nat := 118140960795 + 601982 * 2 ^ 59
def prefixEnd_601982 : Nat := 4983230072969 + 3 ^ 40 * 601982 * 2
def baseEnd_601982 : Nat := 68690246967770883634787

theorem tailTrace_601982 : CollatzResearch.WordTrace tailWord_601982 prefixEnd_601982 68690246967770883634787 := by
  unfold tailWord_601982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744510913141187398195025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14637391536752999457040133 2744510913141187398195025)
  ·
    refine ⟨2058383184855890548646269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2744510913141187398195025 2058383184855890548646269)
    ·
      refine ⟨771893694320958955742351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2058383184855890548646269 771893694320958955742351)
      ·
        refine ⟨1157840541481438433613527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771893694320958955742351 1157840541481438433613527)
        ·
          refine ⟨1736760812222157650420291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157840541481438433613527 1736760812222157650420291)
          ·
            refine ⟨2605141218333236475630437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736760812222157650420291 2605141218333236475630437)
            ·
              refine ⟨488463978437481839180707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2605141218333236475630437 488463978437481839180707)
              ·
                refine ⟨732695967656222758771061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488463978437481839180707 732695967656222758771061)
                ·
                  refine ⟨68690246967770883634787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732695967656222758771061 68690246967770883634787)
                  ·
                    rfl

theorem cell22_601982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_601982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_601982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_601982 prefixEnd_601982 := by exact prefixLift 601982
  have htrace : WordTrace (prefixWord ++ tailWord_601982) baseStart_601982 baseEnd_601982 := by
    simpa [prefixWord, tailWord_601982, baseEnd_601982] using wordTrace_append hprefix tailTrace_601982
  have hstable : (prefixWord ++ tailWord_601982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601982).length < 2 ^ (prefixWord ++ tailWord_601982).sum := by decide
  have hdescent : baseEnd_601982 < baseStart_601982 := by decide
  rcases family_descends (prefixWord ++ tailWord_601982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602012 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_602012 : Nat := 118140960795 + 602012 * 2 ^ 59
def prefixEnd_602012 : Nat := 4983230072969 + 3 ^ 40 * 602012 * 2
def baseEnd_602012 : Nat := 206081010516402572654269

theorem tailTrace_602012 : CollatzResearch.WordTrace tailWord_602012 prefixEnd_602012 206081010516402572654269 := by
  unfold tailWord_602012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10978590747510407154576145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14638120996680542872768193 10978590747510407154576145)
  ·
    refine ⟨8233943060632805365932109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10978590747510407154576145 8233943060632805365932109)
    ·
      refine ⟨3087728647737302012224541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8233943060632805365932109 3087728647737302012224541)
      ·
        refine ⟨1157898242901488254584203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3087728647737302012224541 1157898242901488254584203)
        ·
          refine ⟨1736847364352232381876305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157898242901488254584203 1736847364352232381876305)
          ·
            refine ⟨1302635523264174286407229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736847364352232381876305 1302635523264174286407229)
            ·
              refine ⟨488488321224065357402711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1302635523264174286407229 488488321224065357402711)
              ·
                refine ⟨732732481836098036104067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488488321224065357402711 732732481836098036104067)
                ·
                  refine ⟨1099098722754147054156101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732732481836098036104067 1099098722754147054156101)
                  ·
                    refine ⟨206081010516402572654269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1099098722754147054156101 206081010516402572654269)
                    ·
                      rfl

theorem cell22_602012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_602012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602012 prefixEnd_602012 := by exact prefixLift 602012
  have htrace : WordTrace (prefixWord ++ tailWord_602012) baseStart_602012 baseEnd_602012 := by
    simpa [prefixWord, tailWord_602012, baseEnd_602012] using wordTrace_append hprefix tailTrace_602012
  have hstable : (prefixWord ++ tailWord_602012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602012).length < 2 ^ (prefixWord ++ tailWord_602012).sum := by decide
  have hdescent : baseEnd_602012 < baseStart_602012 := by decide
  rcases family_descends (prefixWord ++ tailWord_602012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602083 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 7]
def baseStart_602083 : Nat := 118140960795 + 602083 * 2 ^ 59
def prefixEnd_602083 : Nat := 4983230072969 + 3 ^ 40 * 602083 * 2
def baseEnd_602083 : Nat := 68701771755794018043017

theorem tailTrace_602083 : CollatzResearch.WordTrace tailWord_602083 prefixEnd_602083 68701771755794018043017 := by
  unfold tailWord_602083
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959771077763593434986903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14639847385175728956657935 21959771077763593434986903)
  ·
    refine ⟨32939656616645390152480355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21959771077763593434986903 32939656616645390152480355)
    ·
      refine ⟨49409484924968085228720533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32939656616645390152480355 49409484924968085228720533)
      ·
        refine ⟨2316069605857878995096275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49409484924968085228720533 2316069605857878995096275)
        ·
          refine ⟨3474104408786818492644413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316069605857878995096275 3474104408786818492644413)
          ·
            refine ⟨1302789153295056934741655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3474104408786818492644413 1302789153295056934741655)
            ·
              refine ⟨1954183729942585402112483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302789153295056934741655 1954183729942585402112483)
              ·
                refine ⟨2931275594913878103168725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954183729942585402112483 2931275594913878103168725)
                ·
                  refine ⟨68701771755794018043017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2931275594913878103168725 68701771755794018043017)
                  ·
                    rfl

theorem cell22_602083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_602083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602083 prefixEnd_602083 := by exact prefixLift 602083
  have htrace : WordTrace (prefixWord ++ tailWord_602083) baseStart_602083 baseEnd_602083 := by
    simpa [prefixWord, tailWord_602083, baseEnd_602083] using wordTrace_append hprefix tailTrace_602083
  have hstable : (prefixWord ++ tailWord_602083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602083).length < 2 ^ (prefixWord ++ tailWord_602083).sum := by decide
  have hdescent : baseEnd_602083 < baseStart_602083 := by decide
  rcases family_descends (prefixWord ++ tailWord_602083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602087 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 3, 3]
def baseStart_602087 : Nat := 118140960795 + 602087 * 2 ^ 59
def prefixEnd_602087 : Nat := 4983230072969 + 3 ^ 40 * 602087 * 2
def baseEnd_602087 : Nat := 206106684549127377029039

theorem tailTrace_602087 : CollatzResearch.WordTrace tailWord_602087 prefixEnd_602087 206106684549127377029039 := by
  unfold tailWord_602087
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959916969749102118132515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14639944646499401412088343 21959916969749102118132515)
  ·
    refine ⟨32939875454623653177198773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21959916969749102118132515 32939875454623653177198773)
    ·
      refine ⟨3088113323870967485362385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32939875454623653177198773 3088113323870967485362385)
      ·
        refine ⟨2316084992903225614021789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3088113323870967485362385 2316084992903225614021789)
        ·
          refine ⟨868531872338709605258171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2316084992903225614021789 868531872338709605258171)
          ·
            refine ⟨1302797808508064407887257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868531872338709605258171 1302797808508064407887257)
            ·
              refine ⟨977098356381048305915443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302797808508064407887257 977098356381048305915443)
              ·
                refine ⟨1465647534571572458873165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977098356381048305915443 1465647534571572458873165)
                ·
                  refine ⟨549617825464339672077437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1465647534571572458873165 549617825464339672077437)
                  ·
                    refine ⟨206106684549127377029039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549617825464339672077437 206106684549127377029039)
                    ·
                      rfl

theorem cell22_602087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_602087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602087 prefixEnd_602087 := by exact prefixLift 602087
  have htrace : WordTrace (prefixWord ++ tailWord_602087) baseStart_602087 baseEnd_602087 := by
    simpa [prefixWord, tailWord_602087, baseEnd_602087] using wordTrace_append hprefix tailTrace_602087
  have hstable : (prefixWord ++ tailWord_602087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602087).length < 2 ^ (prefixWord ++ tailWord_602087).sum := by decide
  have hdescent : baseEnd_602087 < baseStart_602087 := by decide
  rcases family_descends (prefixWord ++ tailWord_602087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602151 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 5]
def baseStart_602151 : Nat := 118140960795 + 602151 * 2 ^ 59
def prefixEnd_602151 : Nat := 4983230072969 + 3 ^ 40 * 602151 * 2
def baseEnd_602151 : Nat := 68709531019017514476281

theorem tailTrace_602151 : CollatzResearch.WordTrace tailWord_602151 prefixEnd_602151 68709531019017514476281 := by
  unfold tailWord_602151
  simp only [CollatzResearch.WordTrace]
  refine ⟨21962251241517241048462307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14641500827678160698974871 21962251241517241048462307)
  ·
    refine ⟨32943376862275861572693461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21962251241517241048462307 32943376862275861572693461)
    ·
      refine ⟨772110395209590505610003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32943376862275861572693461 772110395209590505610003)
      ·
        refine ⟨1158165592814385758415005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772110395209590505610003 1158165592814385758415005)
        ·
          refine ⟨434312097305394659405627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1158165592814385758415005 434312097305394659405627)
          ·
            refine ⟨651468145958091989108441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434312097305394659405627 651468145958091989108441)
            ·
              refine ⟨488601109468568991831331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651468145958091989108441 488601109468568991831331)
              ·
                refine ⟨732901664202853487746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488601109468568991831331 732901664202853487746997)
                ·
                  refine ⟨68709531019017514476281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732901664202853487746997 68709531019017514476281)
                  ·
                    rfl

theorem cell22_602151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 5].length) (baseStart_602151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602151 prefixEnd_602151 := by exact prefixLift 602151
  have htrace : WordTrace (prefixWord ++ tailWord_602151) baseStart_602151 baseEnd_602151 := by
    simpa [prefixWord, tailWord_602151, baseEnd_602151] using wordTrace_append hprefix tailTrace_602151
  have hstable : (prefixWord ++ tailWord_602151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602151).length < 2 ^ (prefixWord ++ tailWord_602151).sum := by decide
  have hdescent : baseEnd_602151 < baseStart_602151 := by decide
  rcases family_descends (prefixWord ++ tailWord_602151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602173 : List Nat := [1, 4, 1, 3, 1, 1, 1, 10]
def baseStart_602173 : Nat := 118140960795 + 602173 * 2 ^ 59
def prefixEnd_602173 : Nat := 4983230072969 + 3 ^ 40 * 602173 * 2
def baseEnd_602173 : Nat := 22904013789627979930975

theorem tailTrace_602173 : CollatzResearch.WordTrace tailWord_602173 prefixEnd_602173 22904013789627979930975 := by
  unfold tailWord_602173
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963053647437538805763173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14642035764958359203842115 21963053647437538805763173)
  ·
    refine ⟨4118072558894538526080595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21963053647437538805763173 4118072558894538526080595)
    ·
      refine ⟨6177108838341807789120893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118072558894538526080595 6177108838341807789120893)
      ·
        refine ⟨2316415814378177920920335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6177108838341807789120893 2316415814378177920920335)
        ·
          refine ⟨3474623721567266881380503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316415814378177920920335 3474623721567266881380503)
          ·
            refine ⟨5211935582350900322070755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474623721567266881380503 5211935582350900322070755)
            ·
              refine ⟨7817903373526350483106133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5211935582350900322070755 7817903373526350483106133)
              ·
                refine ⟨22904013789627979930975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7817903373526350483106133 22904013789627979930975)
                ·
                  rfl

theorem cell22_602173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 10].length) (baseStart_602173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602173 prefixEnd_602173 := by exact prefixLift 602173
  have htrace : WordTrace (prefixWord ++ tailWord_602173) baseStart_602173 baseEnd_602173 := by
    simpa [prefixWord, tailWord_602173, baseEnd_602173] using wordTrace_append hprefix tailTrace_602173
  have hstable : (prefixWord ++ tailWord_602173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602173).length < 2 ^ (prefixWord ++ tailWord_602173).sum := by decide
  have hdescent : baseEnd_602173 < baseStart_602173 := by decide
  rcases family_descends (prefixWord ++ tailWord_602173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602194 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_602194 : Nat := 118140960795 + 602194 * 2 ^ 59
def prefixEnd_602194 : Nat := 4983230072969 + 3 ^ 40 * 602194 * 2
def baseEnd_602194 : Nat := 206143312835814764603711

theorem tailTrace_602194 : CollatzResearch.WordTrace tailWord_602194 prefixEnd_602194 206143312835814764603711 := by
  unfold tailWord_602194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5490954895090364848069409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14642546386907639594851757 5490954895090364848069409)
  ·
    refine ⟨4118216171317773636052057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5490954895090364848069409 4118216171317773636052057)
    ·
      refine ⟨3088662128488330227039043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4118216171317773636052057 3088662128488330227039043)
      ·
        refine ⟨4632993192732495340558565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3088662128488330227039043 4632993192732495340558565)
        ·
          refine ⟨868686223637342876354731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4632993192732495340558565 868686223637342876354731)
          ·
            refine ⟨1303029335456014314532097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868686223637342876354731 1303029335456014314532097)
            ·
              refine ⟨977272001592010735899073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303029335456014314532097 977272001592010735899073)
              ·
                refine ⟨732954001194008051924305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977272001592010735899073 732954001194008051924305)
                ·
                  refine ⟨549715500895506038943229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732954001194008051924305 549715500895506038943229)
                  ·
                    refine ⟨206143312835814764603711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549715500895506038943229 206143312835814764603711)
                    ·
                      rfl

theorem cell22_602194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_602194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602194 prefixEnd_602194 := by exact prefixLift 602194
  have htrace : WordTrace (prefixWord ++ tailWord_602194) baseStart_602194 baseEnd_602194 := by
    simpa [prefixWord, tailWord_602194, baseEnd_602194] using wordTrace_append hprefix tailTrace_602194
  have hstable : (prefixWord ++ tailWord_602194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602194).length < 2 ^ (prefixWord ++ tailWord_602194).sum := by decide
  have hdescent : baseEnd_602194 < baseStart_602194 := by decide
  rcases family_descends (prefixWord ++ tailWord_602194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602222 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_602222 : Nat := 118140960795 + 602222 * 2 ^ 59
def prefixEnd_602222 : Nat := 4983230072969 + 3 ^ 40 * 602222 * 2
def baseEnd_602222 : Nat := 206152897808032024903625

theorem tailTrace_602222 : CollatzResearch.WordTrace tailWord_602222 prefixEnd_602222 206152897808032024903625 := by
  unfold tailWord_602222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745605103032502521787115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14643227216173346782864613 2745605103032502521787115)
  ·
    refine ⟨4118407654548753782680673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2745605103032502521787115 4118407654548753782680673)
    ·
      refine ⟨3088805740911565337010505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4118407654548753782680673 3088805740911565337010505)
      ·
        refine ⟨2316604305683674002757879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3088805740911565337010505 2316604305683674002757879)
        ·
          refine ⟨3474906458525511004136819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316604305683674002757879 3474906458525511004136819)
          ·
            refine ⟨5212359687788266506205229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474906458525511004136819 5212359687788266506205229)
            ·
              refine ⟨1954634882920599939826961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5212359687788266506205229 1954634882920599939826961)
              ·
                refine ⟨1465976162190449954870221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954634882920599939826961 1465976162190449954870221)
                ·
                  refine ⟨549741060821418733076333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1465976162190449954870221 549741060821418733076333)
                  ·
                    refine ⟨206152897808032024903625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549741060821418733076333 206152897808032024903625)
                    ·
                      rfl

theorem cell22_602222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_602222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602222 prefixEnd_602222 := by exact prefixLift 602222
  have htrace : WordTrace (prefixWord ++ tailWord_602222) baseStart_602222 baseEnd_602222 := by
    simpa [prefixWord, tailWord_602222, baseEnd_602222] using wordTrace_append hprefix tailTrace_602222
  have hstable : (prefixWord ++ tailWord_602222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602222).length < 2 ^ (prefixWord ++ tailWord_602222).sum := by decide
  have hdescent : baseEnd_602222 < baseStart_602222 := by decide
  rcases family_descends (prefixWord ++ tailWord_602222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602250 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_602250 : Nat := 118140960795 + 602250 * 2 ^ 59
def prefixEnd_602250 : Nat := 4983230072969 + 3 ^ 40 * 602250 * 2
def baseEnd_602250 : Nat := 206162482780249285203539

theorem tailTrace_602250 : CollatzResearch.WordTrace tailWord_602250 prefixEnd_602250 206162482780249285203539 := by
  unfold tailWord_602250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491465517039645239079051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14643908045439053970877469 5491465517039645239079051)
  ·
    refine ⟨8237198275559467858618577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5491465517039645239079051 8237198275559467858618577)
    ·
      refine ⟨6177898706669600893963933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8237198275559467858618577 6177898706669600893963933)
      ·
        refine ⟨2316712015001100335236475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6177898706669600893963933 2316712015001100335236475)
        ·
          refine ⟨3475068022501650502854713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316712015001100335236475 3475068022501650502854713)
          ·
            refine ⟨2606301016876237877141035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3475068022501650502854713 2606301016876237877141035)
            ·
              refine ⟨3909451525314356815711553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606301016876237877141035 3909451525314356815711553)
              ·
                refine ⟨2932088643985767611783665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3909451525314356815711553 2932088643985767611783665)
                ·
                  refine ⟨2199066482989325708837749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2932088643985767611783665 2199066482989325708837749)
                  ·
                    refine ⟨206162482780249285203539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2199066482989325708837749 206162482780249285203539)
                    ·
                      rfl

theorem cell22_602250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_602250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602250 prefixEnd_602250 := by exact prefixLift 602250
  have htrace : WordTrace (prefixWord ++ tailWord_602250) baseStart_602250 baseEnd_602250 := by
    simpa [prefixWord, tailWord_602250, baseEnd_602250] using wordTrace_append hprefix tailTrace_602250
  have hstable : (prefixWord ++ tailWord_602250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602250).length < 2 ^ (prefixWord ++ tailWord_602250).sum := by decide
  have hdescent : baseEnd_602250 < baseStart_602250 := by decide
  rcases family_descends (prefixWord ++ tailWord_602250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602262 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_602262 : Nat := 118140960795 + 602262 * 2 ^ 59
def prefixEnd_602262 : Nat := 4983230072969 + 3 ^ 40 * 602262 * 2
def baseEnd_602262 : Nat := 206166590625485253903503

theorem tailTrace_602262 : CollatzResearch.WordTrace tailWord_602262 prefixEnd_602262 206166590625485253903503 := by
  unfold tailWord_602262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372893734007194187859565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14644199829410071337168693 1372893734007194187859565)
  ·
    refine ⟨514835150252697820447337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1372893734007194187859565 514835150252697820447337)
    ·
      refine ⟨386126362689523365335503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514835150252697820447337 386126362689523365335503)
      ·
        refine ⟨579189544034285048003255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386126362689523365335503 579189544034285048003255)
        ·
          refine ⟨868784316051427572004883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579189544034285048003255 868784316051427572004883)
          ·
            refine ⟨1303176474077141358007325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868784316051427572004883 1303176474077141358007325)
            ·
              refine ⟨488691177778928009252747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303176474077141358007325 488691177778928009252747)
              ·
                refine ⟨733036766668392013879121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488691177778928009252747 733036766668392013879121)
                ·
                  refine ⟨549777575001294010409341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733036766668392013879121 549777575001294010409341)
                  ·
                    refine ⟨206166590625485253903503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549777575001294010409341 206166590625485253903503)
                    ·
                      rfl

theorem cell22_602262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_602262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602262 prefixEnd_602262 := by exact prefixLift 602262
  have htrace : WordTrace (prefixWord ++ tailWord_602262) baseStart_602262 baseEnd_602262 := by
    simpa [prefixWord, tailWord_602262, baseEnd_602262] using wordTrace_append hprefix tailTrace_602262
  have hstable : (prefixWord ++ tailWord_602262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602262).length < 2 ^ (prefixWord ++ tailWord_602262).sum := by decide
  have hdescent : baseEnd_602262 < baseStart_602262 := by decide
  rcases family_descends (prefixWord ++ tailWord_602262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602312 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_602312 : Nat := 118140960795 + 602312 * 2 ^ 59
def prefixEnd_602312 : Nat := 4983230072969 + 3 ^ 40 * 602312 * 2
def baseEnd_602312 : Nat := 206183706647301790153349

theorem tailTrace_602312 : CollatzResearch.WordTrace tailWord_602312 prefixEnd_602312 206183706647301790153349 := by
  unfold tailWord_602312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984061696966982772536595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14645415595955977030048793 10984061696966982772536595)
  ·
    refine ⟨16476092545450474158804893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10984061696966982772536595 16476092545450474158804893)
    ·
      refine ⟨6178534704543927809551835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16476092545450474158804893 6178534704543927809551835)
      ·
        refine ⟨9267802056815891714327753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6178534704543927809551835 9267802056815891714327753)
        ·
          refine ⟨6950851542611918785745815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9267802056815891714327753 6950851542611918785745815)
          ·
            refine ⟨10426277313917878178618723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950851542611918785745815 10426277313917878178618723)
            ·
              refine ⟨15639415970876817267928085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10426277313917878178618723 15639415970876817267928085)
              ·
                refine ⟨733097623634850809434129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15639415970876817267928085 733097623634850809434129)
                ·
                  refine ⟨549823217726138107075597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733097623634850809434129 549823217726138107075597)
                  ·
                    refine ⟨206183706647301790153349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549823217726138107075597 206183706647301790153349)
                    ·
                      rfl

theorem cell22_602312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_602312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602312 prefixEnd_602312 := by exact prefixLift 602312
  have htrace : WordTrace (prefixWord ++ tailWord_602312) baseStart_602312 baseEnd_602312 := by
    simpa [prefixWord, tailWord_602312, baseEnd_602312] using wordTrace_append hprefix tailTrace_602312
  have hstable : (prefixWord ++ tailWord_602312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602312).length < 2 ^ (prefixWord ++ tailWord_602312).sum := by decide
  have hdescent : baseEnd_602312 < baseStart_602312 := by decide
  rcases family_descends (prefixWord ++ tailWord_602312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602314 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_602314 : Nat := 118140960795 + 602314 * 2 ^ 59
def prefixEnd_602314 : Nat := 4983230072969 + 3 ^ 40 * 602314 * 2
def baseEnd_602314 : Nat := 68728130429391483867781

theorem tailTrace_602314 : CollatzResearch.WordTrace tailWord_602314 prefixEnd_602314 68728130429391483867781 := by
  unfold tailWord_602314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492049084981679971661499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14645464226617813257763997 5492049084981679971661499)
  ·
    refine ⟨8238073627472519957492249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5492049084981679971661499 8238073627472519957492249)
    ·
      refine ⟨6178555220604389968119187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8238073627472519957492249 6178555220604389968119187)
      ·
        refine ⟨9267832830906584952178781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6178555220604389968119187 9267832830906584952178781)
        ·
          refine ⟨3475437311589969357067043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9267832830906584952178781 3475437311589969357067043)
          ·
            refine ⟨5213155967384954035600565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475437311589969357067043 5213155967384954035600565)
            ·
              refine ⟨488733371942339440837553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5213155967384954035600565 488733371942339440837553)
              ·
                refine ⟨366550028956754580628165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488733371942339440837553 366550028956754580628165)
                ·
                  refine ⟨68728130429391483867781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366550028956754580628165 68728130429391483867781)
                  ·
                    rfl

theorem cell22_602314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_602314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602314 prefixEnd_602314 := by exact prefixLift 602314
  have htrace : WordTrace (prefixWord ++ tailWord_602314) baseStart_602314 baseEnd_602314 := by
    simpa [prefixWord, tailWord_602314, baseEnd_602314] using wordTrace_append hprefix tailTrace_602314
  have hstable : (prefixWord ++ tailWord_602314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602314).length < 2 ^ (prefixWord ++ tailWord_602314).sum := by decide
  have hdescent : baseEnd_602314 < baseStart_602314 := by decide
  rcases family_descends (prefixWord ++ tailWord_602314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602329 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 2, 3]
def baseStart_602329 : Nat := 118140960795 + 602329 * 2 ^ 59
def prefixEnd_602329 : Nat := 4983230072969 + 3 ^ 40 * 602329 * 2
def baseEnd_602329 : Nat := 206189526094719412478297

theorem tailTrace_602329 : CollatzResearch.WordTrace tailWord_602329 prefixEnd_602329 206189526094719412478297 := by
  unfold tailWord_602329
  simp only [CollatzResearch.WordTrace]
  refine ⟨21968743434872377448442041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14645828956581584965628027 21968743434872377448442041)
  ·
    refine ⟨16476557576154283086331531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21968743434872377448442041 16476557576154283086331531)
    ·
      refine ⟨24714836364231424629497297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16476557576154283086331531 24714836364231424629497297)
      ·
        refine ⟨18536127273173568472122973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24714836364231424629497297 18536127273173568472122973)
        ·
          refine ⟨6951047727440088177046115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18536127273173568472122973 6951047727440088177046115)
          ·
            refine ⟨10426571591160132265569173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951047727440088177046115 10426571591160132265569173)
            ·
              refine ⟨488745543335631199948555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10426571591160132265569173 488745543335631199948555)
              ·
                refine ⟨733118315003446799922833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488745543335631199948555 733118315003446799922833)
                ·
                  refine ⟨549838736252585099942125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733118315003446799922833 549838736252585099942125)
                  ·
                    refine ⟨206189526094719412478297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549838736252585099942125 206189526094719412478297)
                    ·
                      rfl

theorem cell22_602329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_602329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602329 prefixEnd_602329 := by exact prefixLift 602329
  have htrace : WordTrace (prefixWord ++ tailWord_602329) baseStart_602329 baseEnd_602329 := by
    simpa [prefixWord, tailWord_602329, baseEnd_602329] using wordTrace_append hprefix tailTrace_602329
  have hstable : (prefixWord ++ tailWord_602329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602329).length < 2 ^ (prefixWord ++ tailWord_602329).sum := by decide
  have hdescent : baseEnd_602329 < baseStart_602329 := by decide
  rcases family_descends (prefixWord ++ tailWord_602329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602385 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_602385 : Nat := 118140960795 + 602385 * 2 ^ 59
def prefixEnd_602385 : Nat := 4983230072969 + 3 ^ 40 * 602385 * 2
def baseEnd_602385 : Nat := 206208696039153933078125

theorem tailTrace_602385 : CollatzResearch.WordTrace tailWord_602385 prefixEnd_602385 206208696039153933078125 := by
  unfold tailWord_602385
  simp only [CollatzResearch.WordTrace]
  refine ⟨21970785922669499012480609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14647190615112999341653739 21970785922669499012480609)
  ·
    refine ⟨16478089442002124259360457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21970785922669499012480609 16478089442002124259360457)
    ·
      refine ⟨12358567081501593194520343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16478089442002124259360457 12358567081501593194520343)
      ·
        refine ⟨18537850622252389791780515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12358567081501593194520343 18537850622252389791780515)
        ·
          refine ⟨27806775933378584687670773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18537850622252389791780515 27806775933378584687670773)
          ·
            refine ⟨2606885243754242314469135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27806775933378584687670773 2606885243754242314469135)
            ·
              refine ⟨3910327865631363471703703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606885243754242314469135 3910327865631363471703703)
              ·
                refine ⟨5865491798447045207555555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910327865631363471703703 5865491798447045207555555)
                ·
                  refine ⟨8798237697670567811333333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5865491798447045207555555 8798237697670567811333333)
                  ·
                    refine ⟨206208696039153933078125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8798237697670567811333333 206208696039153933078125)
                    ·
                      rfl

theorem cell22_602385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_602385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602385 prefixEnd_602385 := by exact prefixLift 602385
  have htrace : WordTrace (prefixWord ++ tailWord_602385) baseStart_602385 baseEnd_602385 := by
    simpa [prefixWord, tailWord_602385, baseEnd_602385] using wordTrace_append hprefix tailTrace_602385
  have hstable : (prefixWord ++ tailWord_602385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602385).length < 2 ^ (prefixWord ++ tailWord_602385).sum := by decide
  have hdescent : baseEnd_602385 < baseStart_602385 := by decide
  rcases family_descends (prefixWord ++ tailWord_602385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602408 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 1, 3]
def baseStart_602408 : Nat := 118140960795 + 602408 * 2 ^ 59
def prefixEnd_602408 : Nat := 4983230072969 + 3 ^ 40 * 602408 * 2
def baseEnd_602408 : Nat := 206216569409189539753055

theorem tailTrace_602408 : CollatzResearch.WordTrace tailWord_602408 prefixEnd_602408 206216569409189539753055 := by
  unfold tailWord_602408
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985812400793086970283939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14647749867724115960378585 10985812400793086970283939)
  ·
    refine ⟨16478718601189630455425909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10985812400793086970283939 16478718601189630455425909)
    ·
      refine ⟨1544879868861527855196179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16478718601189630455425909 1544879868861527855196179)
      ·
        refine ⟨2317319803292291782794269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544879868861527855196179 2317319803292291782794269)
        ·
          refine ⟨868994926234609418547851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2317319803292291782794269 868994926234609418547851)
          ·
            refine ⟨1303492389351914127821777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868994926234609418547851 1303492389351914127821777)
            ·
              refine ⟨977619292013935595866333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303492389351914127821777 977619292013935595866333)
              ·
                refine ⟨366607234505225848449875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977619292013935595866333 366607234505225848449875)
                ·
                  refine ⟨549910851757838772674813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366607234505225848449875 549910851757838772674813)
                  ·
                    refine ⟨206216569409189539753055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549910851757838772674813 206216569409189539753055)
                    ·
                      rfl

theorem cell22_602408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_602408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602408 prefixEnd_602408 := by exact prefixLift 602408
  have htrace : WordTrace (prefixWord ++ tailWord_602408) baseStart_602408 baseEnd_602408 := by
    simpa [prefixWord, tailWord_602408, baseEnd_602408] using wordTrace_append hprefix tailTrace_602408
  have hstable : (prefixWord ++ tailWord_602408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602408).length < 2 ^ (prefixWord ++ tailWord_602408).sum := by decide
  have hdescent : baseEnd_602408 < baseStart_602408 := by decide
  rcases family_descends (prefixWord ++ tailWord_602408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602466 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_602466 : Nat := 118140960795 + 602466 * 2 ^ 59
def prefixEnd_602466 : Nat := 4983230072969 + 3 ^ 40 * 602466 * 2
def baseEnd_602466 : Nat := 68745474664832240600959

theorem tailTrace_602466 : CollatzResearch.WordTrace tailWord_602466 prefixEnd_602466 68745474664832240600959 := by
  unfold tailWord_602466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493435058844012461544813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14649160156917366564119501 5493435058844012461544813)
  ·
    refine ⟨2060038147066504673079305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5493435058844012461544813 2060038147066504673079305)
    ·
      refine ⟨1545028610299878504809479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060038147066504673079305 1545028610299878504809479)
      ·
        refine ⟨2317542915449817757214219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545028610299878504809479 2317542915449817757214219)
        ·
          refine ⟨3476314373174726635821329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317542915449817757214219 3476314373174726635821329)
          ·
            refine ⟨2607235779881044976865997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3476314373174726635821329 2607235779881044976865997)
            ·
              refine ⟨977713417455391866324749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2607235779881044976865997 977713417455391866324749)
              ·
                refine ⟨366642531545771949871781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977713417455391866324749 366642531545771949871781)
                ·
                  refine ⟨68745474664832240600959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366642531545771949871781 68745474664832240600959)
                  ·
                    rfl

theorem cell22_602466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_602466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602466 prefixEnd_602466 := by exact prefixLift 602466
  have htrace : WordTrace (prefixWord ++ tailWord_602466) baseStart_602466 baseEnd_602466 := by
    simpa [prefixWord, tailWord_602466, baseEnd_602466] using wordTrace_append hprefix tailTrace_602466
  have hstable : (prefixWord ++ tailWord_602466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602466).length < 2 ^ (prefixWord ++ tailWord_602466).sum := by decide
  have hdescent : baseEnd_602466 < baseStart_602466 := by decide
  rcases family_descends (prefixWord ++ tailWord_602466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602475 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_602475 : Nat := 118140960795 + 602475 * 2 ^ 59
def prefixEnd_602475 : Nat := 4983230072969 + 3 ^ 40 * 602475 * 2
def baseEnd_602475 : Nat := 206239504878423698327849

theorem tailTrace_602475 : CollatzResearch.WordTrace tailWord_602475 prefixEnd_602475 206239504878423698327849 := by
  unfold tailWord_602475
  simp only [CollatzResearch.WordTrace]
  refine ⟨21974068492343444383256879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14649378994895629588837919 21974068492343444383256879)
  ·
    refine ⟨32961102738515166574885319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21974068492343444383256879 32961102738515166574885319)
    ·
      refine ⟨49441654107772749862327979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32961102738515166574885319 49441654107772749862327979)
      ·
        refine ⟨74162481161659124793491969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49441654107772749862327979 74162481161659124793491969)
        ·
          refine ⟨55621860871244343595118977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74162481161659124793491969 55621860871244343595118977)
          ·
            refine ⟨41716395653433257696339233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55621860871244343595118977 41716395653433257696339233)
            ·
              refine ⟨31287296740074943272254425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41716395653433257696339233 31287296740074943272254425)
              ·
                refine ⟨23465472555056207454190819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31287296740074943272254425 23465472555056207454190819)
                ·
                  refine ⟨35198208832584311181286229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23465472555056207454190819 35198208832584311181286229)
                  ·
                    refine ⟨206239504878423698327849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35198208832584311181286229 206239504878423698327849)
                    ·
                      rfl

theorem cell22_602475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_602475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602475 prefixEnd_602475 := by exact prefixLift 602475
  have htrace : WordTrace (prefixWord ++ tailWord_602475) baseStart_602475 baseEnd_602475 := by
    simpa [prefixWord, tailWord_602475, baseEnd_602475] using wordTrace_append hprefix tailTrace_602475
  have hstable : (prefixWord ++ tailWord_602475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602475).length < 2 ^ (prefixWord ++ tailWord_602475).sum := by decide
  have hdescent : baseEnd_602475 < baseStart_602475 := by decide
  rcases family_descends (prefixWord ++ tailWord_602475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602567 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 8]
def baseStart_602567 : Nat := 118140960795 + 602567 * 2 ^ 59
def prefixEnd_602567 : Nat := 4983230072969 + 3 ^ 40 * 602567 * 2
def baseEnd_602567 : Nat := 68756999452855375009189

theorem tailTrace_602567 : CollatzResearch.WordTrace tailWord_602567 prefixEnd_602567 68756999452855375009189 := by
  unfold tailWord_602567
  simp only [CollatzResearch.WordTrace]
  refine ⟨21977424008010144095605955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14651616005340096063737303 21977424008010144095605955)
  ·
    refine ⟨32966136012015216143408933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21977424008010144095605955 32966136012015216143408933)
    ·
      refine ⟨6181150502252853026889175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32966136012015216143408933 6181150502252853026889175)
      ·
        refine ⟨9271725753379279540333763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6181150502252853026889175 9271725753379279540333763)
        ·
          refine ⟨13907588630068919310500645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9271725753379279540333763 13907588630068919310500645)
          ·
            refine ⟨2607672868137922370718871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13907588630068919310500645 2607672868137922370718871)
            ·
              refine ⟨3911509302206883556078307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607672868137922370718871 3911509302206883556078307)
              ·
                refine ⟨5867263953310325334117461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911509302206883556078307 5867263953310325334117461)
                ·
                  refine ⟨68756999452855375009189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5867263953310325334117461 68756999452855375009189)
                  ·
                    rfl

theorem cell22_602567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_602567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602567 prefixEnd_602567 := by exact prefixLift 602567
  have htrace : WordTrace (prefixWord ++ tailWord_602567) baseStart_602567 baseEnd_602567 := by
    simpa [prefixWord, tailWord_602567, baseEnd_602567] using wordTrace_append hprefix tailTrace_602567
  have hstable : (prefixWord ++ tailWord_602567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602567).length < 2 ^ (prefixWord ++ tailWord_602567).sum := by decide
  have hdescent : baseEnd_602567 < baseStart_602567 := by decide
  rcases family_descends (prefixWord ++ tailWord_602567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602614 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_602614 : Nat := 118140960795 + 602614 * 2 ^ 59
def prefixEnd_602614 : Nat := 4983230072969 + 3 ^ 40 * 602614 * 2
def baseEnd_602614 : Nat := 206287087419073669102423

theorem tailTrace_602614 : CollatzResearch.WordTrace tailWord_602614 prefixEnd_602614 206287087419073669102423 := by
  unfold tailWord_602614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373696139927491945160431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14652758825893247415044597 1373696139927491945160431)
  ·
    refine ⟨2060544209891237917740647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373696139927491945160431 2060544209891237917740647)
    ·
      refine ⟨3090816314836856876610971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060544209891237917740647 3090816314836856876610971)
      ·
        refine ⟨4636224472255285314916457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090816314836856876610971 4636224472255285314916457)
        ·
          refine ⟨3477168354191463986187343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4636224472255285314916457 3477168354191463986187343)
          ·
            refine ⟨5215752531287195979281015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477168354191463986187343 5215752531287195979281015)
            ·
              refine ⟨7823628796930793968921523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215752531287195979281015 7823628796930793968921523)
              ·
                refine ⟨11735443195396190953382285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7823628796930793968921523 11735443195396190953382285)
                ·
                  refine ⟨4400791198273571607518357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11735443195396190953382285 4400791198273571607518357)
                  ·
                    refine ⟨206287087419073669102423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4400791198273571607518357 206287087419073669102423)
                    ·
                      rfl

theorem cell22_602614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_602614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602614 prefixEnd_602614 := by exact prefixLift 602614
  have htrace : WordTrace (prefixWord ++ tailWord_602614) baseStart_602614 baseEnd_602614 := by
    simpa [prefixWord, tailWord_602614, baseEnd_602614] using wordTrace_append hprefix tailTrace_602614
  have hstable : (prefixWord ++ tailWord_602614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602614).length < 2 ^ (prefixWord ++ tailWord_602614).sum := by decide
  have hdescent : baseEnd_602614 < baseStart_602614 := by decide
  rcases family_descends (prefixWord ++ tailWord_602614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602627 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_602627 : Nat := 118140960795 + 602627 * 2 ^ 59
def prefixEnd_602627 : Nat := 4983230072969 + 3 ^ 40 * 602627 * 2
def baseEnd_602627 : Nat := 206291537584745968527383

theorem tailTrace_602627 : CollatzResearch.WordTrace tailWord_602627 prefixEnd_602627 206291537584745968527383 := by
  unfold tailWord_602627
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979612387792774342790135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14653074925195182895193423 21979612387792774342790135)
  ·
    refine ⟨32969418581689161514185203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21979612387792774342790135 32969418581689161514185203)
    ·
      refine ⟨49454127872533742271277805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32969418581689161514185203 49454127872533742271277805)
      ·
        refine ⟨18545297952200153351729177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49454127872533742271277805 18545297952200153351729177)
        ·
          refine ⟨13908973464150115013796883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18545297952200153351729177 13908973464150115013796883)
          ·
            refine ⟨20863460196225172520695325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13908973464150115013796883 20863460196225172520695325)
            ·
              refine ⟨7823797573584439695260747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20863460196225172520695325 7823797573584439695260747)
              ·
                refine ⟨11735696360376659542891121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7823797573584439695260747 11735696360376659542891121)
                ·
                  refine ⟨8801772270282494657168341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11735696360376659542891121 8801772270282494657168341)
                  ·
                    refine ⟨206291537584745968527383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8801772270282494657168341 206291537584745968527383)
                    ·
                      rfl

theorem cell22_602627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_602627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602627 prefixEnd_602627 := by exact prefixLift 602627
  have htrace : WordTrace (prefixWord ++ tailWord_602627) baseStart_602627 baseEnd_602627 := by
    simpa [prefixWord, tailWord_602627, baseEnd_602627] using wordTrace_append hprefix tailTrace_602627
  have hstable : (prefixWord ++ tailWord_602627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602627).length < 2 ^ (prefixWord ++ tailWord_602627).sum := by decide
  have hdescent : baseEnd_602627 < baseStart_602627 := by decide
  rcases family_descends (prefixWord ++ tailWord_602627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602629 : List Nat := [1, 3, 1, 1, 2, 2, 6, 6]
def baseStart_602629 : Nat := 118140960795 + 602629 * 2 ^ 59
def prefixEnd_602629 : Nat := 4983230072969 + 3 ^ 40 * 602629 * 2
def baseEnd_602629 : Nat := 22921358025068736664153

theorem tailTrace_602629 : CollatzResearch.WordTrace tailWord_602629 prefixEnd_602629 22921358025068736664153 := by
  unfold tailWord_602629
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979685333785528684362941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14653123555857019122908627 21979685333785528684362941)
  ·
    refine ⟨8242382000169573256636103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21979685333785528684362941 8242382000169573256636103)
    ·
      refine ⟨12363573000254359884954155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242382000169573256636103 12363573000254359884954155)
      ·
        refine ⟨18545359500381539827431233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12363573000254359884954155 18545359500381539827431233)
        ·
          refine ⟨13909019625286154870573425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18545359500381539827431233 13909019625286154870573425)
          ·
            refine ⟨10431764718964616152930069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13909019625286154870573425 10431764718964616152930069)
            ·
              refine ⟨488988971201466382168597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10431764718964616152930069 488988971201466382168597)
              ·
                refine ⟨22921358025068736664153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 488988971201466382168597 22921358025068736664153)
                ·
                  rfl

theorem cell22_602629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 6].length) (baseStart_602629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602629 prefixEnd_602629 := by exact prefixLift 602629
  have htrace : WordTrace (prefixWord ++ tailWord_602629) baseStart_602629 baseEnd_602629 := by
    simpa [prefixWord, tailWord_602629, baseEnd_602629] using wordTrace_append hprefix tailTrace_602629
  have hstable : (prefixWord ++ tailWord_602629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602629).length < 2 ^ (prefixWord ++ tailWord_602629).sum := by decide
  have hdescent : baseEnd_602629 < baseStart_602629 := by decide
  rcases family_descends (prefixWord ++ tailWord_602629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602661 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_602661 : Nat := 118140960795 + 602661 * 2 ^ 59
def prefixEnd_602661 : Nat := 4983230072969 + 3 ^ 40 * 602661 * 2
def baseEnd_602661 : Nat := 206303176479581213177279

theorem tailTrace_602661 : CollatzResearch.WordTrace tailWord_602661 prefixEnd_602661 206303176479581213177279 := by
  unfold tailWord_602661
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980852469669598149527837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14653901646446398766351891 21980852469669598149527837)
  ·
    refine ⟨8242819676126099306072939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21980852469669598149527837 8242819676126099306072939)
    ·
      refine ⟨12364229514189148959109409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242819676126099306072939 12364229514189148959109409)
      ·
        refine ⟨9273172135641861719332057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12364229514189148959109409 9273172135641861719332057)
        ·
          refine ⟨6954879101731396289499043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9273172135641861719332057 6954879101731396289499043)
          ·
            refine ⟨10432318652597094434248565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6954879101731396289499043 10432318652597094434248565)
            ·
              refine ⟨978029873680977603210803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10432318652597094434248565 978029873680977603210803)
              ·
                refine ⟨1467044810521466404816205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978029873680977603210803 1467044810521466404816205)
                ·
                  refine ⟨550141803945549901806077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1467044810521466404816205 550141803945549901806077)
                  ·
                    refine ⟨206303176479581213177279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550141803945549901806077 206303176479581213177279)
                    ·
                      rfl

theorem cell22_602661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_602661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602661 prefixEnd_602661 := by exact prefixLift 602661
  have htrace : WordTrace (prefixWord ++ tailWord_602661) baseStart_602661 baseEnd_602661 := by
    simpa [prefixWord, tailWord_602661, baseEnd_602661] using wordTrace_append hprefix tailTrace_602661
  have hstable : (prefixWord ++ tailWord_602661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602661).length < 2 ^ (prefixWord ++ tailWord_602661).sum := by decide
  have hdescent : baseEnd_602661 < baseStart_602661 := by decide
  rcases family_descends (prefixWord ++ tailWord_602661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602663 : List Nat := [1, 1, 7, 2, 1, 1, 2, 7]
def baseStart_602663 : Nat := 118140960795 + 602663 * 2 ^ 59
def prefixEnd_602663 : Nat := 4983230072969 + 3 ^ 40 * 602663 * 2
def baseEnd_602663 : Nat := 22922651235605986069697

theorem tailTrace_602663 : CollatzResearch.WordTrace tailWord_602663 prefixEnd_602663 22922651235605986069697 := by
  unfold tailWord_602663
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980925415662352491100643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14653950277108234994067095 21980925415662352491100643)
  ·
    refine ⟨32971388123493528736650965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21980925415662352491100643 32971388123493528736650965)
    ·
      refine ⟨772766909144379579765257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32971388123493528736650965 772766909144379579765257)
      ·
        refine ⟨579575181858284684823943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 772766909144379579765257 579575181858284684823943)
        ·
          refine ⟨869362772787427027235915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579575181858284684823943 869362772787427027235915)
          ·
            refine ⟨1304044159181140540853873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869362772787427027235915 1304044159181140540853873)
            ·
              refine ⟨978033119385855405640405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304044159181140540853873 978033119385855405640405)
              ·
                refine ⟨22922651235605986069697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 978033119385855405640405 22922651235605986069697)
                ·
                  rfl

theorem cell22_602663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 7].length) (baseStart_602663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602663 prefixEnd_602663 := by exact prefixLift 602663
  have htrace : WordTrace (prefixWord ++ tailWord_602663) baseStart_602663 baseEnd_602663 := by
    simpa [prefixWord, tailWord_602663, baseEnd_602663] using wordTrace_append hprefix tailTrace_602663
  have hstable : (prefixWord ++ tailWord_602663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602663).length < 2 ^ (prefixWord ++ tailWord_602663).sum := by decide
  have hdescent : baseEnd_602663 < baseStart_602663 := by decide
  rcases family_descends (prefixWord ++ tailWord_602663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602736 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_602736 : Nat := 118140960795 + 602736 * 2 ^ 59
def prefixEnd_602736 : Nat := 4983230072969 + 3 ^ 40 * 602736 * 2
def baseEnd_602736 : Nat := 68776283504102005850683

theorem tailTrace_602736 : CollatzResearch.WordTrace tailWord_602736 prefixEnd_602736 68776283504102005850683 := by
  unfold tailWord_602736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991793972198942979254031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14655725296265257305672041 10991793972198942979254031)
  ·
    refine ⟨16487690958298414468881047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10991793972198942979254031 16487690958298414468881047)
    ·
      refine ⟨24731536437447621703321571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16487690958298414468881047 24731536437447621703321571)
      ·
        refine ⟨37097304656171432554982357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24731536437447621703321571 37097304656171432554982357)
        ·
          refine ⟨869468077879017950507399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37097304656171432554982357 869468077879017950507399)
          ·
            refine ⟨1304202116818526925761099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869468077879017950507399 1304202116818526925761099)
            ·
              refine ⟨1956303175227790388641649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304202116818526925761099 1956303175227790388641649)
              ·
                refine ⟨1467227381420842791481237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956303175227790388641649 1467227381420842791481237)
                ·
                  refine ⟨68776283504102005850683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1467227381420842791481237 68776283504102005850683)
                  ·
                    rfl

theorem cell22_602736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_602736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602736 prefixEnd_602736 := by exact prefixLift 602736
  have htrace : WordTrace (prefixWord ++ tailWord_602736) baseStart_602736 baseEnd_602736 := by
    simpa [prefixWord, tailWord_602736, baseEnd_602736] using wordTrace_append hprefix tailTrace_602736
  have hstable : (prefixWord ++ tailWord_602736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602736).length < 2 ^ (prefixWord ++ tailWord_602736).sum := by decide
  have hdescent : baseEnd_602736 < baseStart_602736 := by decide
  rcases family_descends (prefixWord ++ tailWord_602736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602753 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 4]
def baseStart_602753 : Nat := 118140960795 + 602753 * 2 ^ 59
def prefixEnd_602753 : Nat := 4983230072969 + 3 ^ 40 * 602753 * 2
def baseEnd_602753 : Nat := 68778223319907879958999

theorem tailTrace_602753 : CollatzResearch.WordTrace tailWord_602753 prefixEnd_602753 68778223319907879958999 := by
  unfold tailWord_602753
  simp only [CollatzResearch.WordTrace]
  refine ⟨21984207985336297861876913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14656138656890865241251275 21984207985336297861876913)
  ·
    refine ⟨16488155989002223396407685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21984207985336297861876913 16488155989002223396407685)
    ·
      refine ⟨3091529247937916886826441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16488155989002223396407685 3091529247937916886826441)
      ·
        refine ⟨2318646935953437665119831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3091529247937916886826441 2318646935953437665119831)
        ·
          refine ⟨3477970403930156497679747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318646935953437665119831 3477970403930156497679747)
          ·
            refine ⟨5216955605895234746519621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477970403930156497679747 5216955605895234746519621)
            ·
              refine ⟨978179176105356514972429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5216955605895234746519621 978179176105356514972429)
              ·
                refine ⟨366817191039508693114661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 978179176105356514972429 366817191039508693114661)
                ·
                  refine ⟨68778223319907879958999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366817191039508693114661 68778223319907879958999)
                  ·
                    rfl

theorem cell22_602753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_602753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602753 prefixEnd_602753 := by exact prefixLift 602753
  have htrace : WordTrace (prefixWord ++ tailWord_602753) baseStart_602753 baseEnd_602753 := by
    simpa [prefixWord, tailWord_602753, baseEnd_602753] using wordTrace_append hprefix tailTrace_602753
  have hstable : (prefixWord ++ tailWord_602753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602753).length < 2 ^ (prefixWord ++ tailWord_602753).sum := by decide
  have hdescent : baseEnd_602753 < baseStart_602753 := by decide
  rcases family_descends (prefixWord ++ tailWord_602753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602766 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_602766 : Nat := 118140960795 + 602766 * 2 ^ 59
def prefixEnd_602766 : Nat := 4983230072969 + 3 ^ 40 * 602766 * 2
def baseEnd_602766 : Nat := 206339120125395939301957

theorem tailTrace_602766 : CollatzResearch.WordTrace tailWord_602766 prefixEnd_602766 206339120125395939301957 := by
  unfold tailWord_602766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748085266786150135262519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14656454756192800721400101 2748085266786150135262519)
  ·
    refine ⟨4122127900179225202893779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748085266786150135262519 4122127900179225202893779)
    ·
      refine ⟨6183191850268837804340669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4122127900179225202893779 6183191850268837804340669)
      ·
        refine ⟨2318696943850814176627751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6183191850268837804340669 2318696943850814176627751)
        ·
          refine ⟨3478045415776221264941627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318696943850814176627751 3478045415776221264941627)
          ·
            refine ⟨5217068123664331897412441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478045415776221264941627 5217068123664331897412441)
            ·
              refine ⟨3912801092748248923059331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5217068123664331897412441 3912801092748248923059331)
              ·
                refine ⟨5869201639122373384588997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912801092748248923059331 5869201639122373384588997)
                ·
                  refine ⟨1100475307335445009610437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5869201639122373384588997 1100475307335445009610437)
                  ·
                    refine ⟨206339120125395939301957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1100475307335445009610437 206339120125395939301957)
                    ·
                      rfl

theorem cell22_602766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_602766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602766 prefixEnd_602766 := by exact prefixLift 602766
  have htrace : WordTrace (prefixWord ++ tailWord_602766) baseStart_602766 baseEnd_602766 := by
    simpa [prefixWord, tailWord_602766, baseEnd_602766] using wordTrace_append hprefix tailTrace_602766
  have hstable : (prefixWord ++ tailWord_602766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602766).length < 2 ^ (prefixWord ++ tailWord_602766).sum := by decide
  have hdescent : baseEnd_602766 < baseStart_602766 := by decide
  rcases family_descends (prefixWord ++ tailWord_602766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602785 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 1, 5]
def baseStart_602785 : Nat := 118140960795 + 602785 * 2 ^ 59
def prefixEnd_602785 : Nat := 4983230072969 + 3 ^ 40 * 602785 * 2
def baseEnd_602785 : Nat := 206345624213686223076899

theorem tailTrace_602785 : CollatzResearch.WordTrace tailWord_602785 prefixEnd_602785 206345624213686223076899 := by
  unfold tailWord_602785
  simp only [CollatzResearch.WordTrace]
  refine ⟨21985375121220367327041809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14656916747480244884694539 21985375121220367327041809)
  ·
    refine ⟨16489031340915275495281357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21985375121220367327041809 16489031340915275495281357)
    ·
      refine ⟨6183386752843228310730509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16489031340915275495281357 6183386752843228310730509)
      ·
        refine ⟨2318770032316210616523941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6183386752843228310730509 2318770032316210616523941)
        ·
          refine ⟨434769381059289490598239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2318770032316210616523941 434769381059289490598239)
          ·
            refine ⟨652154071588934235897359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434769381059289490598239 652154071588934235897359)
            ·
              refine ⟨978231107383401353846039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652154071588934235897359 978231107383401353846039)
              ·
                refine ⟨1467346661075102030769059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978231107383401353846039 1467346661075102030769059)
                ·
                  refine ⟨2201019991612653046153589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467346661075102030769059 2201019991612653046153589)
                  ·
                    refine ⟨206345624213686223076899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2201019991612653046153589 206345624213686223076899)
                    ·
                      rfl

theorem cell22_602785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_602785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602785 prefixEnd_602785 := by exact prefixLift 602785
  have htrace : WordTrace (prefixWord ++ tailWord_602785) baseStart_602785 baseEnd_602785 := by
    simpa [prefixWord, tailWord_602785, baseEnd_602785] using wordTrace_append hprefix tailTrace_602785
  have hstable : (prefixWord ++ tailWord_602785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602785).length < 2 ^ (prefixWord ++ tailWord_602785).sum := by decide
  have hdescent : baseEnd_602785 < baseStart_602785 := by decide
  rcases family_descends (prefixWord ++ tailWord_602785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602798 : List Nat := [4, 1, 4, 1, 1, 2, 1, 8]
def baseStart_602798 : Nat := 118140960795 + 602798 * 2 ^ 59
def prefixEnd_602798 : Nat := 4983230072969 + 3 ^ 40 * 602798 * 2
def baseEnd_602798 : Nat := 22927786042150946944651

theorem tailTrace_602798 : CollatzResearch.WordTrace tailWord_602798 prefixEnd_602798 22927786042150946944651 := by
  unfold tailWord_602798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748231158771658818408131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14657232846782180364843365 2748231158771658818408131)
  ·
    refine ⟨4122346738157488227612197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748231158771658818408131 4122346738157488227612197)
    ·
      refine ⟨772940013404529042677287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4122346738157488227612197 772940013404529042677287)
      ·
        refine ⟨1159410020106793564015931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772940013404529042677287 1159410020106793564015931)
        ·
          refine ⟨1739115030160190346023897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159410020106793564015931 1739115030160190346023897)
          ·
            refine ⟨1304336272620142759517923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1739115030160190346023897 1304336272620142759517923)
            ·
              refine ⟨1956504408930214139276885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304336272620142759517923 1956504408930214139276885)
              ·
                refine ⟨22927786042150946944651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1956504408930214139276885 22927786042150946944651)
                ·
                  rfl

theorem cell22_602798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_602798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602798 prefixEnd_602798 := by exact prefixLift 602798
  have htrace : WordTrace (prefixWord ++ tailWord_602798) baseStart_602798 baseEnd_602798 := by
    simpa [prefixWord, tailWord_602798, baseEnd_602798] using wordTrace_append hprefix tailTrace_602798
  have hstable : (prefixWord ++ tailWord_602798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602798).length < 2 ^ (prefixWord ++ tailWord_602798).sum := by decide
  have hdescent : baseEnd_602798 < baseStart_602798 := by decide
  rcases family_descends (prefixWord ++ tailWord_602798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602826 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_602826 : Nat := 118140960795 + 602826 * 2 ^ 59
def prefixEnd_602826 : Nat := 4983230072969 + 3 ^ 40 * 602826 * 2
def baseEnd_602826 : Nat := 68786553117191927600591

theorem tailTrace_602826 : CollatzResearch.WordTrace tailWord_602826 prefixEnd_602826 68786553117191927600591 := by
  unfold tailWord_602826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496717628517957832321083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14657913676047887552856221 5496717628517957832321083)
  ·
    refine ⟨8245076442776936748481625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496717628517957832321083 8245076442776936748481625)
    ·
      refine ⟨6183807332082702561361219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8245076442776936748481625 6183807332082702561361219)
      ·
        refine ⟨9275710998124053842041829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183807332082702561361219 9275710998124053842041829)
        ·
          refine ⟨1739195812148260095382843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9275710998124053842041829 1739195812148260095382843)
          ·
            refine ⟨2608793718222390143074265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739195812148260095382843 2608793718222390143074265)
            ·
              refine ⟨1956595288666792607305699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2608793718222390143074265 1956595288666792607305699)
              ·
                refine ⟨2934892933000188910958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956595288666792607305699 2934892933000188910958549)
                ·
                  refine ⟨68786553117191927600591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2934892933000188910958549 68786553117191927600591)
                  ·
                    rfl

theorem cell22_602826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_602826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602826 prefixEnd_602826 := by exact prefixLift 602826
  have htrace : WordTrace (prefixWord ++ tailWord_602826) baseStart_602826 baseEnd_602826 := by
    simpa [prefixWord, tailWord_602826, baseEnd_602826] using wordTrace_append hprefix tailTrace_602826
  have hstable : (prefixWord ++ tailWord_602826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602826).length < 2 ^ (prefixWord ++ tailWord_602826).sum := by decide
  have hdescent : baseEnd_602826 < baseStart_602826 := by decide
  rcases family_descends (prefixWord ++ tailWord_602826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602830 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_602830 : Nat := 118140960795 + 602830 * 2 ^ 59
def prefixEnd_602830 : Nat := 4983230072969 + 3 ^ 40 * 602830 * 2
def baseEnd_602830 : Nat := 206361028633321105701761

theorem tailTrace_602830 : CollatzResearch.WordTrace tailWord_602830 prefixEnd_602830 206361028633321105701761 := by
  unfold tailWord_602830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748377050757167501553743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14658010937371560008286629 2748377050757167501553743)
  ·
    refine ⟨4122565576135751252330615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748377050757167501553743 4122565576135751252330615)
    ·
      refine ⟨6183848364203626878495923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4122565576135751252330615 6183848364203626878495923)
      ·
        refine ⟨9275772546305440317743885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183848364203626878495923 9275772546305440317743885)
        ·
          refine ⟨3478414704864540119153957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9275772546305440317743885 3478414704864540119153957)
          ·
            refine ⟨652202757162101272341367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3478414704864540119153957 652202757162101272341367)
            ·
              refine ⟨978304135743151908512051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652202757162101272341367 978304135743151908512051)
              ·
                refine ⟨1467456203614727862768077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978304135743151908512051 1467456203614727862768077)
                ·
                  refine ⟨550296076355522948538029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1467456203614727862768077 550296076355522948538029)
                  ·
                    refine ⟨206361028633321105701761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550296076355522948538029 206361028633321105701761)
                    ·
                      rfl

theorem cell22_602830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_602830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602830 prefixEnd_602830 := by exact prefixLift 602830
  have htrace : WordTrace (prefixWord ++ tailWord_602830) baseStart_602830 baseEnd_602830 := by
    simpa [prefixWord, tailWord_602830, baseEnd_602830] using wordTrace_append hprefix tailTrace_602830
  have hstable : (prefixWord ++ tailWord_602830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602830).length < 2 ^ (prefixWord ++ tailWord_602830).sum := by decide
  have hdescent : baseEnd_602830 < baseStart_602830 := by decide
  rcases family_descends (prefixWord ++ tailWord_602830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602901 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_602901 : Nat := 118140960795 + 602901 * 2 ^ 59
def prefixEnd_602901 : Nat := 4983230072969 + 3 ^ 40 * 602901 * 2
def baseEnd_602901 : Nat := 206385333384300587176543

theorem tailTrace_602901 : CollatzResearch.WordTrace tailWord_602901 prefixEnd_602901 206385333384300587176543 := by
  unfold tailWord_602901
  simp only [CollatzResearch.WordTrace]
  refine ⟨21989605988800119138264557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14659737325866746092176371 21989605988800119138264557)
  ·
    refine ⟨8246102245800044676849209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21989605988800119138264557 8246102245800044676849209)
    ·
      refine ⟨6184576684350033507636907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8246102245800044676849209 6184576684350033507636907)
      ·
        refine ⟨9276865026525050261455361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6184576684350033507636907 9276865026525050261455361)
        ·
          refine ⟨6957648769893787696091521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9276865026525050261455361 6957648769893787696091521)
          ·
            refine ⟨5218236577420340772068641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957648769893787696091521 5218236577420340772068641)
            ·
              refine ⟨3913677433065255579051481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5218236577420340772068641 3913677433065255579051481)
              ·
                refine ⟨2935258074798941684288611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3913677433065255579051481 2935258074798941684288611)
                ·
                  refine ⟨4402887112198412526432917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935258074798941684288611 4402887112198412526432917)
                  ·
                    refine ⟨206385333384300587176543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4402887112198412526432917 206385333384300587176543)
                    ·
                      rfl

theorem cell22_602901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_602901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_602901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_602901 prefixEnd_602901 := by exact prefixLift 602901
  have htrace : WordTrace (prefixWord ++ tailWord_602901) baseStart_602901 baseEnd_602901 := by
    simpa [prefixWord, tailWord_602901, baseEnd_602901] using wordTrace_append hprefix tailTrace_602901
  have hstable : (prefixWord ++ tailWord_602901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602901).length < 2 ^ (prefixWord ++ tailWord_602901).sum := by decide
  have hdescent : baseEnd_602901 < baseStart_602901 := by decide
  rcases family_descends (prefixWord ++ tailWord_602901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603057 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 4]
def baseStart_603057 : Nat := 118140960795 + 603057 * 2 ^ 59
def prefixEnd_603057 : Nat := 4983230072969 + 3 ^ 40 * 603057 * 2
def baseEnd_603057 : Nat := 68812911790789393425355

theorem tailTrace_603057 : CollatzResearch.WordTrace tailWord_603057 prefixEnd_603057 68812911790789393425355 := by
  unfold tailWord_603057
  simp only [CollatzResearch.WordTrace]
  refine ⟨21995295776234957780943425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14663530517489971853962283 21995295776234957780943425)
  ·
    refine ⟨16496471832176218335707569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21995295776234957780943425 16496471832176218335707569)
    ·
      refine ⟨12372353874132163751780677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16496471832176218335707569 12372353874132163751780677)
      ·
        refine ⟨2319816351399780703458877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12372353874132163751780677 2319816351399780703458877)
        ·
          refine ⟨869931131774917763797079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2319816351399780703458877 869931131774917763797079)
          ·
            refine ⟨1304896697662376645695619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869931131774917763797079 1304896697662376645695619)
            ·
              refine ⟨1957345046493564968543429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304896697662376645695619 1957345046493564968543429)
              ·
                refine ⟨367002196217543431601893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1957345046493564968543429 367002196217543431601893)
                ·
                  refine ⟨68812911790789393425355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367002196217543431601893 68812911790789393425355)
                  ·
                    rfl

theorem cell22_603057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_603057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603057 prefixEnd_603057 := by exact prefixLift 603057
  have htrace : WordTrace (prefixWord ++ tailWord_603057) baseStart_603057 baseEnd_603057 := by
    simpa [prefixWord, tailWord_603057, baseEnd_603057] using wordTrace_append hprefix tailTrace_603057
  have hstable : (prefixWord ++ tailWord_603057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603057).length < 2 ^ (prefixWord ++ tailWord_603057).sum := by decide
  have hdescent : baseEnd_603057 < baseStart_603057 := by decide
  rcases family_descends (prefixWord ++ tailWord_603057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603106 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_603106 : Nat := 118140960795 + 603106 * 2 ^ 59
def prefixEnd_603106 : Nat := 4983230072969 + 3 ^ 40 * 603106 * 2
def baseEnd_603106 : Nat := 206455509073748385800915

theorem tailTrace_603106 : CollatzResearch.WordTrace tailWord_603106 prefixEnd_603106 206455509073748385800915 := by
  unfold tailWord_603106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499270738264359787369293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14664721968704959432984781 5499270738264359787369293)
  ·
    refine ⟨2062226526849134920263485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5499270738264359787369293 2062226526849134920263485)
    ·
      refine ⟨773334947568425595098807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2062226526849134920263485 773334947568425595098807)
      ·
        refine ⟨1160002421352638392648211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773334947568425595098807 1160002421352638392648211)
        ·
          refine ⟨1740003632028957588972317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160002421352638392648211 1740003632028957588972317)
          ·
            refine ⟨652501362010859095864619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1740003632028957588972317 652501362010859095864619)
            ·
              refine ⟨978752043016288643796929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652501362010859095864619 978752043016288643796929)
              ·
                refine ⟨734064032262216482847697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978752043016288643796929 734064032262216482847697)
                ·
                  refine ⟨550548024196662362135773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 734064032262216482847697 550548024196662362135773)
                  ·
                    refine ⟨206455509073748385800915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550548024196662362135773 206455509073748385800915)
                    ·
                      rfl

theorem cell22_603106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_603106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603106 prefixEnd_603106 := by exact prefixLift 603106
  have htrace : WordTrace (prefixWord ++ tailWord_603106) baseStart_603106 baseEnd_603106 := by
    simpa [prefixWord, tailWord_603106, baseEnd_603106] using wordTrace_append hprefix tailTrace_603106
  have hstable : (prefixWord ++ tailWord_603106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603106).length < 2 ^ (prefixWord ++ tailWord_603106).sum := by decide
  have hdescent : baseEnd_603106 < baseStart_603106 := by decide
  rcases family_descends (prefixWord ++ tailWord_603106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603168 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 1, 3]
def baseStart_603168 : Nat := 118140960795 + 603168 * 2 ^ 59
def prefixEnd_603168 : Nat := 4983230072969 + 3 ^ 40 * 603168 * 2
def baseEnd_603168 : Nat := 206476732940800890750725

theorem tailTrace_603168 : CollatzResearch.WordTrace tailWord_603168 prefixEnd_603168 206476732940800890750725 := by
  unfold tailWord_603168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999672139416411869117079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14666229519221882492156105 10999672139416411869117079)
  ·
    refine ⟨16499508209124617803675619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10999672139416411869117079 16499508209124617803675619)
    ·
      refine ⟨24749262313686926705513429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16499508209124617803675619 24749262313686926705513429)
      ·
        refine ⟨580060835477037344660471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24749262313686926705513429 580060835477037344660471)
        ·
          refine ⟨870091253215556016990707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580060835477037344660471 870091253215556016990707)
          ·
            refine ⟨1305136879823334025486061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870091253215556016990707 1305136879823334025486061)
            ·
              refine ⟨489426329933750259557273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1305136879823334025486061 489426329933750259557273)
              ·
                refine ⟨367069747450312694667955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489426329933750259557273 367069747450312694667955)
                ·
                  refine ⟨550604621175469042001933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367069747450312694667955 550604621175469042001933)
                  ·
                    refine ⟨206476732940800890750725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550604621175469042001933 206476732940800890750725)
                    ·
                      rfl

theorem cell22_603168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_603168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603168 prefixEnd_603168 := by exact prefixLift 603168
  have htrace : WordTrace (prefixWord ++ tailWord_603168) baseStart_603168 baseEnd_603168 := by
    simpa [prefixWord, tailWord_603168, baseEnd_603168] using wordTrace_append hprefix tailTrace_603168
  have hstable : (prefixWord ++ tailWord_603168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603168).length < 2 ^ (prefixWord ++ tailWord_603168).sum := by decide
  have hdescent : baseEnd_603168 < baseStart_603168 := by decide
  rcases family_descends (prefixWord ++ tailWord_603168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603203 : List Nat := [1, 1, 1, 3, 1, 2, 3, 10]
def baseStart_603203 : Nat := 118140960795 + 603203 * 2 ^ 59
def prefixEnd_603203 : Nat := 4983230072969 + 3 ^ 40 * 603203 * 2
def baseEnd_603203 : Nat := 22943190461785829569513

theorem tailTrace_603203 : CollatzResearch.WordTrace tailWord_603203 prefixEnd_603203 22943190461785829569513 := by
  unfold tailWord_603203
  simp only [CollatzResearch.WordTrace]
  refine ⟨22000620833706024715758263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14667080555804016477172175 22000620833706024715758263)
  ·
    refine ⟨33000931250559037073637395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22000620833706024715758263 33000931250559037073637395)
    ·
      refine ⟨49501396875838555610456093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33000931250559037073637395 49501396875838555610456093)
      ·
        refine ⟨18563023828439458353921035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49501396875838555610456093 18563023828439458353921035)
        ·
          refine ⟨27844535742659187530881553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18563023828439458353921035 27844535742659187530881553)
          ·
            refine ⟨20883401806994390648161165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27844535742659187530881553 20883401806994390648161165)
            ·
              refine ⟨7831275677622896493060437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20883401806994390648161165 7831275677622896493060437)
              ·
                refine ⟨22943190461785829569513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7831275677622896493060437 22943190461785829569513)
                ·
                  rfl

theorem cell22_603203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 10].length) (baseStart_603203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603203 prefixEnd_603203 := by exact prefixLift 603203
  have htrace : WordTrace (prefixWord ++ tailWord_603203) baseStart_603203 baseEnd_603203 := by
    simpa [prefixWord, tailWord_603203, baseEnd_603203] using wordTrace_append hprefix tailTrace_603203
  have hstable : (prefixWord ++ tailWord_603203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603203).length < 2 ^ (prefixWord ++ tailWord_603203).sum := by decide
  have hdescent : baseEnd_603203 < baseStart_603203 := by decide
  rcases family_descends (prefixWord ++ tailWord_603203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603205 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_603205 : Nat := 118140960795 + 603205 * 2 ^ 59
def prefixEnd_603205 : Nat := 4983230072969 + 3 ^ 40 * 603205 * 2
def baseEnd_603205 : Nat := 206489398796945127575611

theorem tailTrace_603205 : CollatzResearch.WordTrace tailWord_603205 prefixEnd_603205 206489398796945127575611 := by
  unfold tailWord_603205
  simp only [CollatzResearch.WordTrace]
  refine ⟨22000693779698779057331069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14667129186465852704887379 22000693779698779057331069)
  ·
    refine ⟨8250260167387042146499151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22000693779698779057331069 8250260167387042146499151)
    ·
      refine ⟨12375390251080563219748727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250260167387042146499151 12375390251080563219748727)
      ·
        refine ⟨18563085376620844829623091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375390251080563219748727 18563085376620844829623091)
        ·
          refine ⟨27844628064931267244434637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18563085376620844829623091 27844628064931267244434637)
          ·
            refine ⟨10441735524349225216662989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27844628064931267244434637 10441735524349225216662989)
            ·
              refine ⟨3915650821630959456248621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10441735524349225216662989 3915650821630959456248621)
              ·
                refine ⟨1468369058111609796093233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3915650821630959456248621 1468369058111609796093233)
                ·
                  refine ⟨1101276793583707347069925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468369058111609796093233 1101276793583707347069925)
                  ·
                    refine ⟨206489398796945127575611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101276793583707347069925 206489398796945127575611)
                    ·
                      rfl

theorem cell22_603205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_603205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603205 prefixEnd_603205 := by exact prefixLift 603205
  have htrace : WordTrace (prefixWord ++ tailWord_603205) baseStart_603205 baseEnd_603205 := by
    simpa [prefixWord, tailWord_603205, baseEnd_603205] using wordTrace_append hprefix tailTrace_603205
  have hstable : (prefixWord ++ tailWord_603205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603205).length < 2 ^ (prefixWord ++ tailWord_603205).sum := by decide
  have hdescent : baseEnd_603205 < baseStart_603205 := by decide
  rcases family_descends (prefixWord ++ tailWord_603205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603250 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_603250 : Nat := 118140960795 + 603250 * 2 ^ 59
def prefixEnd_603250 : Nat := 4983230072969 + 3 ^ 40 * 603250 * 2
def baseEnd_603250 : Nat := 206504803216580010200473

theorem tailTrace_603250 : CollatzResearch.WordTrace tailWord_603250 prefixEnd_603250 206504803216580010200473 := by
  unfold tailWord_603250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500583766133937935679801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14668223376357167828479469 5500583766133937935679801)
  ·
    refine ⟨4125437824600453451759851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500583766133937935679801 4125437824600453451759851)
    ·
      refine ⟨6188156736900680177639777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125437824600453451759851 6188156736900680177639777)
      ·
        refine ⟨4641117552675510133229833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6188156736900680177639777 4641117552675510133229833)
        ·
          refine ⟨3480838164506632599922375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4641117552675510133229833 3480838164506632599922375)
          ·
            refine ⟨5221257246759948899883563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480838164506632599922375 5221257246759948899883563)
            ·
              refine ⟨7831885870139923349825345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221257246759948899883563 7831885870139923349825345)
              ·
                refine ⟨5873914402604942512369009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7831885870139923349825345 5873914402604942512369009)
                ·
                  refine ⟨4405435801953706884276757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873914402604942512369009 4405435801953706884276757)
                  ·
                    refine ⟨206504803216580010200473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4405435801953706884276757 206504803216580010200473)
                    ·
                      rfl

theorem cell22_603250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_603250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603250 prefixEnd_603250 := by exact prefixLift 603250
  have htrace : WordTrace (prefixWord ++ tailWord_603250) baseStart_603250 baseEnd_603250 := by
    simpa [prefixWord, tailWord_603250, baseEnd_603250] using wordTrace_append hprefix tailTrace_603250
  have hstable : (prefixWord ++ tailWord_603250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603250).length < 2 ^ (prefixWord ++ tailWord_603250).sum := by decide
  have hdescent : baseEnd_603250 < baseStart_603250 := by decide
  rcases family_descends (prefixWord ++ tailWord_603250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603262 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_603262 : Nat := 118140960795 + 603262 * 2 ^ 59
def prefixEnd_603262 : Nat := 4983230072969 + 3 ^ 40 * 603262 * 2
def baseEnd_603262 : Nat := 206508911061815978900437

theorem tailTrace_603262 : CollatzResearch.WordTrace tailWord_603262 prefixEnd_603262 206508911061815978900437 := by
  unfold tailWord_603262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750346592561534724019505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14668515160328185194770693 2750346592561534724019505)
  ·
    refine ⟨2062759944421151043014629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2750346592561534724019505 2062759944421151043014629)
    ·
      refine ⟨386767489578965820565243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2062759944421151043014629 386767489578965820565243)
      ·
        refine ⟨580151234368448730847865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386767489578965820565243 580151234368448730847865)
        ·
          refine ⟨435113425776336548135899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580151234368448730847865 435113425776336548135899)
          ·
            refine ⟨652670138664504822203849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435113425776336548135899 652670138664504822203849)
            ·
              refine ⟨489502603998378616652887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652670138664504822203849 489502603998378616652887)
              ·
                refine ⟨734253905997567924979331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489502603998378616652887 734253905997567924979331)
                ·
                  refine ⟨1101380858996351887468997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734253905997567924979331 1101380858996351887468997)
                  ·
                    refine ⟨206508911061815978900437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101380858996351887468997 206508911061815978900437)
                    ·
                      rfl

theorem cell22_603262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_603262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603262 prefixEnd_603262 := by exact prefixLift 603262
  have htrace : WordTrace (prefixWord ++ tailWord_603262) baseStart_603262 baseEnd_603262 := by
    simpa [prefixWord, tailWord_603262, baseEnd_603262] using wordTrace_append hprefix tailTrace_603262
  have hstable : (prefixWord ++ tailWord_603262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603262).length < 2 ^ (prefixWord ++ tailWord_603262).sum := by decide
  have hdescent : baseEnd_603262 < baseStart_603262 := by decide
  rcases family_descends (prefixWord ++ tailWord_603262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603282 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_603282 : Nat := 118140960795 + 603282 * 2 ^ 59
def prefixEnd_603282 : Nat := 4983230072969 + 3 ^ 40 * 603282 * 2
def baseEnd_603282 : Nat := 68838585823514197800125

theorem tailTrace_603282 : CollatzResearch.WordTrace tailWord_603282 prefixEnd_603282 68838585823514197800125 := by
  unfold tailWord_603282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500875550104955301971025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14669001466946547471922733 5500875550104955301971025)
  ·
    refine ⟨4125656662578716476478269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500875550104955301971025 4125656662578716476478269)
    ·
      refine ⟨1547121248467018678679351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4125656662578716476478269 1547121248467018678679351)
      ·
        refine ⟨2320681872700528018019027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547121248467018678679351 2320681872700528018019027)
        ·
          refine ⟨3481022809050792027028541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320681872700528018019027 3481022809050792027028541)
          ·
            refine ⟨1305383553394047010135703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3481022809050792027028541 1305383553394047010135703)
            ·
              refine ⟨1958075330091070515203555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305383553394047010135703 1958075330091070515203555)
              ·
                refine ⟨2937112995136605772805333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958075330091070515203555 2937112995136605772805333)
                ·
                  refine ⟨68838585823514197800125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2937112995136605772805333 68838585823514197800125)
                  ·
                    rfl

theorem cell22_603282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_603282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603282 prefixEnd_603282 := by exact prefixLift 603282
  have htrace : WordTrace (prefixWord ++ tailWord_603282) baseStart_603282 baseEnd_603282 := by
    simpa [prefixWord, tailWord_603282, baseEnd_603282] using wordTrace_append hprefix tailTrace_603282
  have hstable : (prefixWord ++ tailWord_603282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603282).length < 2 ^ (prefixWord ++ tailWord_603282).sum := by decide
  have hdescent : baseEnd_603282 < baseStart_603282 := by decide
  rcases family_descends (prefixWord ++ tailWord_603282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603350 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_603350 : Nat := 118140960795 + 603350 * 2 ^ 59
def prefixEnd_603350 : Nat := 4983230072969 + 3 ^ 40 * 603350 * 2
def baseEnd_603350 : Nat := 68846345086737694233389

theorem tailTrace_603350 : CollatzResearch.WordTrace tailWord_603350 prefixEnd_603350 68846345086737694233389 := by
  unfold tailWord_603350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375373897760841801334969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14670654909448979214239669 1375373897760841801334969)
  ·
    refine ⟨1031530423320631351001227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1375373897760841801334969 1031530423320631351001227)
    ·
      refine ⟨1547295634980947026501841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031530423320631351001227 1547295634980947026501841)
      ·
        refine ⟨1160471726235710269876381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1547295634980947026501841 1160471726235710269876381)
        ·
          refine ⟨435176897338391351203643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1160471726235710269876381 435176897338391351203643)
          ·
            refine ⟨652765346007587026805465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435176897338391351203643 652765346007587026805465)
            ·
              refine ⟨489574009505690270104099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652765346007587026805465 489574009505690270104099)
              ·
                refine ⟨734361014258535405156149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489574009505690270104099 734361014258535405156149)
                ·
                  refine ⟨68846345086737694233389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734361014258535405156149 68846345086737694233389)
                  ·
                    rfl

theorem cell22_603350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_603350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603350 prefixEnd_603350 := by exact prefixLift 603350
  have htrace : WordTrace (prefixWord ++ tailWord_603350) baseStart_603350 baseEnd_603350 := by
    simpa [prefixWord, tailWord_603350, baseEnd_603350] using wordTrace_append hprefix tailTrace_603350
  have hstable : (prefixWord ++ tailWord_603350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603350).length < 2 ^ (prefixWord ++ tailWord_603350).sum := by decide
  have hdescent : baseEnd_603350 < baseStart_603350 := by decide
  rcases family_descends (prefixWord ++ tailWord_603350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603421 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_603421 : Nat := 118140960795 + 603421 * 2 ^ 59
def prefixEnd_603421 : Nat := 4983230072969 + 3 ^ 40 * 603421 * 2
def baseEnd_603421 : Nat := 206563340011192564174949

theorem tailTrace_603421 : CollatzResearch.WordTrace tailWord_603421 prefixEnd_603421 206563340011192564174949 := by
  unfold tailWord_603421
  simp only [CollatzResearch.WordTrace]
  refine ⟨22008571946916247947194117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14672381297944165298129411 22008571946916247947194117)
  ·
    refine ⟨4126607240046796490098897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22008571946916247947194117 4126607240046796490098897)
    ·
      refine ⟨3094955430035097367574173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4126607240046796490098897 3094955430035097367574173)
      ·
        refine ⟨1160608286263161512840315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3094955430035097367574173 1160608286263161512840315)
        ·
          refine ⟨1740912429394742269260473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160608286263161512840315 1740912429394742269260473)
          ·
            refine ⟨1305684322046056701945355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1740912429394742269260473 1305684322046056701945355)
            ·
              refine ⟨1958526483069085052918033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305684322046056701945355 1958526483069085052918033)
              ·
                refine ⟨1468894862301813789688525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958526483069085052918033 1468894862301813789688525)
                ·
                  refine ⟨550835573363180171133197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1468894862301813789688525 550835573363180171133197)
                  ·
                    refine ⟨206563340011192564174949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550835573363180171133197 206563340011192564174949)
                    ·
                      rfl

theorem cell22_603421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_603421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603421 prefixEnd_603421 := by exact prefixLift 603421
  have htrace : WordTrace (prefixWord ++ tailWord_603421) baseStart_603421 baseEnd_603421 := by
    simpa [prefixWord, tailWord_603421, baseEnd_603421] using wordTrace_append hprefix tailTrace_603421
  have hstable : (prefixWord ++ tailWord_603421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603421).length < 2 ^ (prefixWord ++ tailWord_603421).sum := by decide
  have hdescent : baseEnd_603421 < baseStart_603421 := by decide
  rcases family_descends (prefixWord ++ tailWord_603421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603524 : List Nat := [2, 3, 2, 1, 1, 4, 2, 7]
def baseStart_603524 : Nat := 118140960795 + 603524 * 2 ^ 59
def prefixEnd_603524 : Nat := 4983230072969 + 3 ^ 40 * 603524 * 2
def baseEnd_603524 : Nat := 22955399890681625427737

theorem tailTrace_603524 : CollatzResearch.WordTrace tailWord_603524 prefixEnd_603524 22955399890681625427737 := by
  unfold tailWord_603524
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006164332771548269096813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14674885777028731025462417 11006164332771548269096813)
  ·
    refine ⟨4127311624789330600911305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11006164332771548269096813 4127311624789330600911305)
    ·
      refine ⟨3095483718591997950683479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4127311624789330600911305 3095483718591997950683479)
      ·
        refine ⟨4643225577887996926025219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095483718591997950683479 4643225577887996926025219)
        ·
          refine ⟨6964838366831995389037829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643225577887996926025219 6964838366831995389037829)
          ·
            refine ⟨1305907193780999135444593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6964838366831995389037829 1305907193780999135444593)
            ·
              refine ⟨979430395335749351583445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305907193780999135444593 979430395335749351583445)
              ·
                refine ⟨22955399890681625427737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 979430395335749351583445 22955399890681625427737)
                ·
                  rfl

theorem cell22_603524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_603524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603524 prefixEnd_603524 := by exact prefixLift 603524
  have htrace : WordTrace (prefixWord ++ tailWord_603524) baseStart_603524 baseEnd_603524 := by
    simpa [prefixWord, tailWord_603524, baseEnd_603524] using wordTrace_append hprefix tailTrace_603524
  have hstable : (prefixWord ++ tailWord_603524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603524).length < 2 ^ (prefixWord ++ tailWord_603524).sum := by decide
  have hdescent : baseEnd_603524 < baseStart_603524 := by decide
  rcases family_descends (prefixWord ++ tailWord_603524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
