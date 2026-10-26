import V185TrunkScan19Chunk006

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_70397 : List Nat := [1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_70397 : Nat := 118140960795 + 70397 * 2 ^ 59
def prefixEnd_70397 : Nat := 4983230072969 + 3 ^ 40 * 70397 * 2
def baseEnd_70397 : Nat := 21420739339061514141485

theorem tailTrace_70397 : CollatzResearch.WordTrace tailWord_70397 prefixEnd_70397 21420739339061514141485 := by
  unfold tailWord_70397
  simp only [CollatzResearch.WordTrace]
  refine ⟨2567589525971166695521445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1711726350647444463680963 2567589525971166695521445)
  ·
    refine ⟨481423036119593755410271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2567589525971166695521445 481423036119593755410271)
    ·
      refine ⟨722134554179390633115407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481423036119593755410271 722134554179390633115407)
      ·
        refine ⟨1083201831269085949673111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722134554179390633115407 1083201831269085949673111)
        ·
          refine ⟨1624802746903628924509667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083201831269085949673111 1624802746903628924509667)
          ·
            refine ⟨2437204120355443386764501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624802746903628924509667 2437204120355443386764501)
            ·
              refine ⟨57121971570830704377293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2437204120355443386764501 57121971570830704377293)
              ·
                refine ⟨21420739339061514141485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57121971570830704377293 21420739339061514141485)
                ·
                  rfl

theorem cell19_70397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_70397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70397 prefixEnd_70397 := by exact prefixLift 70397
  have htrace : WordTrace (prefixWord ++ tailWord_70397) baseStart_70397 baseEnd_70397 := by
    simpa [prefixWord, tailWord_70397, baseEnd_70397] using wordTrace_append hprefix tailTrace_70397
  have hstable : (prefixWord ++ tailWord_70397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70397).length < 2 ^ (prefixWord ++ tailWord_70397).sum := by decide
  have hdescent : baseEnd_70397 < baseStart_70397 := by decide
  rcases family_descends (prefixWord ++ tailWord_70397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70437 : List Nat := [1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_70437 : Nat := 118140960795 + 70437 * 2 ^ 59
def prefixEnd_70437 : Nat := 4983230072969 + 3 ^ 40 * 70437 * 2
def baseEnd_70437 : Nat := 21432910732353273252487

theorem tailTrace_70437 : CollatzResearch.WordTrace tailWord_70437 prefixEnd_70437 21432910732353273252487 := by
  unfold tailWord_70437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569048445826253526977565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1712698963884169017985043 2569048445826253526977565)
  ·
    refine ⟨963393167184845072616587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2569048445826253526977565 963393167184845072616587)
    ·
      refine ⟨1445089750777267608924881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963393167184845072616587 1445089750777267608924881)
      ·
        refine ⟨1083817313082950706693661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1445089750777267608924881 1083817313082950706693661)
        ·
          refine ⟨406431492406106515010123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1083817313082950706693661 406431492406106515010123)
          ·
            refine ⟨609647238609159772515185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406431492406106515010123 609647238609159772515185)
            ·
              refine ⟨457235428956869829386389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609647238609159772515185 457235428956869829386389)
              ·
                refine ⟨21432910732353273252487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 457235428956869829386389 21432910732353273252487)
                ·
                  rfl

theorem cell19_70437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_70437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70437 prefixEnd_70437 := by exact prefixLift 70437
  have htrace : WordTrace (prefixWord ++ tailWord_70437) baseStart_70437 baseEnd_70437 := by
    simpa [prefixWord, tailWord_70437, baseEnd_70437] using wordTrace_append hprefix tailTrace_70437
  have hstable : (prefixWord ++ tailWord_70437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70437).length < 2 ^ (prefixWord ++ tailWord_70437).sum := by decide
  have hdescent : baseEnd_70437 < baseStart_70437 := by decide
  rcases family_descends (prefixWord ++ tailWord_70437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70452 : List Nat := [2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_70452 : Nat := 118140960795 + 70452 * 2 ^ 59
def prefixEnd_70452 : Nat := 4983230072969 + 3 ^ 40 * 70452 * 2
def baseEnd_70452 : Nat := 21437475004837682919113

theorem tailTrace_70452 : CollatzResearch.WordTrace tailWord_70452 prefixEnd_70452 21437475004837682919113 := by
  unfold tailWord_70452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284797770385955544386805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1713063693847940725849073 1284797770385955544386805)
  ·
    refine ⟨120449790973683332286263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1284797770385955544386805 120449790973683332286263)
    ·
      refine ⟨180674686460524998429395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120449790973683332286263 180674686460524998429395)
      ·
        refine ⟨271012029690787497644093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180674686460524998429395 271012029690787497644093)
        ·
          refine ⟨101629511134045311616535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271012029690787497644093 101629511134045311616535)
          ·
            refine ⟨152444266701067967424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101629511134045311616535 152444266701067967424803)
            ·
              refine ⟨228666400051601951137205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152444266701067967424803 228666400051601951137205)
              ·
                refine ⟨21437475004837682919113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228666400051601951137205 21437475004837682919113)
                ·
                  rfl

theorem cell19_70452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_70452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70452 prefixEnd_70452 := by exact prefixLift 70452
  have htrace : WordTrace (prefixWord ++ tailWord_70452) baseStart_70452 baseEnd_70452 := by
    simpa [prefixWord, tailWord_70452, baseEnd_70452] using wordTrace_append hprefix tailTrace_70452
  have hstable : (prefixWord ++ tailWord_70452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70452).length < 2 ^ (prefixWord ++ tailWord_70452).sum := by decide
  have hdescent : baseEnd_70452 < baseStart_70452 := by decide
  rcases family_descends (prefixWord ++ tailWord_70452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70456 : List Nat := [2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_70456 : Nat := 118140960795 + 70456 * 2 ^ 59
def prefixEnd_70456 : Nat := 4983230072969 + 3 ^ 40 * 70456 * 2
def baseEnd_70456 : Nat := 21438692144166858830213

theorem tailTrace_70456 : CollatzResearch.WordTrace tailWord_70456 prefixEnd_70456 21438692144166858830213 := by
  unfold tailWord_70456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284870716378709885959611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1713160955171613181279481 1284870716378709885959611)
  ·
    refine ⟨1927306074568064828939417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1284870716378709885959611 1927306074568064828939417)
    ·
      refine ⟨1445479555926048621704563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1927306074568064828939417 1445479555926048621704563)
      ·
        refine ⟨2168219333889072932556845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445479555926048621704563 2168219333889072932556845)
        ·
          refine ⟨813082250208402349708817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2168219333889072932556845 813082250208402349708817)
          ·
            refine ⟨609811687656301762281613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 813082250208402349708817 609811687656301762281613)
            ·
              refine ⟨228679382871113160855605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609811687656301762281613 228679382871113160855605)
              ·
                refine ⟨21438692144166858830213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228679382871113160855605 21438692144166858830213)
                ·
                  rfl

theorem cell19_70456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_70456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70456 prefixEnd_70456 := by exact prefixLift 70456
  have htrace : WordTrace (prefixWord ++ tailWord_70456) baseStart_70456 baseEnd_70456 := by
    simpa [prefixWord, tailWord_70456, baseEnd_70456] using wordTrace_append hprefix tailTrace_70456
  have hstable : (prefixWord ++ tailWord_70456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70456).length < 2 ^ (prefixWord ++ tailWord_70456).sum := by decide
  have hdescent : baseEnd_70456 < baseStart_70456 := by decide
  rcases family_descends (prefixWord ++ tailWord_70456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70492 : List Nat := [2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_70492 : Nat := 118140960795 + 70492 * 2 ^ 59
def prefixEnd_70492 : Nat := 4983230072969 + 3 ^ 40 * 70492 * 2
def baseEnd_70492 : Nat := 21449646398129442030115

theorem tailTrace_70492 : CollatzResearch.WordTrace tailWord_70492 prefixEnd_70492 21449646398129442030115 := by
  unfold tailWord_70492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285527230313498960114865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1714036307084665280153153 1285527230313498960114865)
  ·
    refine ⟨964145422735124220086149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1285527230313498960114865 964145422735124220086149)
    ·
      refine ⟨180777266762835791266153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 964145422735124220086149 180777266762835791266153)
      ·
        refine ⟨135582950072126843449615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180777266762835791266153 135582950072126843449615)
        ·
          refine ⟨203374425108190265174423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135582950072126843449615 203374425108190265174423)
          ·
            refine ⟨305061637662285397761635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203374425108190265174423 305061637662285397761635)
            ·
              refine ⟨457592456493428096642453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305061637662285397761635 457592456493428096642453)
              ·
                refine ⟨21449646398129442030115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 457592456493428096642453 21449646398129442030115)
                ·
                  rfl

theorem cell19_70492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_70492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70492 prefixEnd_70492 := by exact prefixLift 70492
  have htrace : WordTrace (prefixWord ++ tailWord_70492) baseStart_70492 baseEnd_70492 := by
    simpa [prefixWord, tailWord_70492, baseEnd_70492] using wordTrace_append hprefix tailTrace_70492
  have hstable : (prefixWord ++ tailWord_70492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70492).length < 2 ^ (prefixWord ++ tailWord_70492).sum := by decide
  have hdescent : baseEnd_70492 < baseStart_70492 := by decide
  rcases family_descends (prefixWord ++ tailWord_70492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70513 : List Nat := [1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_70513 : Nat := 118140960795 + 70513 * 2 ^ 59
def prefixEnd_70513 : Nat := 4983230072969 + 3 ^ 40 * 70513 * 2
def baseEnd_70513 : Nat := 21456036379607615563391

theorem tailTrace_70513 : CollatzResearch.WordTrace tailWord_70513 prefixEnd_70513 21456036379607615563391 := by
  unfold tailWord_70513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571820393550918506744193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1714546929033945671162795 2571820393550918506744193)
  ·
    refine ⟨1928865295163188880058145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2571820393550918506744193 1928865295163188880058145)
    ·
      refine ⟨1446648971372391660043609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1928865295163188880058145 1446648971372391660043609)
      ·
        refine ⟨1084986728529293745032707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1446648971372391660043609 1084986728529293745032707)
        ·
          refine ⟨1627480092793940617549061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084986728529293745032707 1627480092793940617549061)
          ·
            refine ⟨305152517398863865790449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1627480092793940617549061 305152517398863865790449)
            ·
              refine ⟨228864388049147899342837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305152517398863865790449 228864388049147899342837)
              ·
                refine ⟨21456036379607615563391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228864388049147899342837 21456036379607615563391)
                ·
                  rfl

theorem cell19_70513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_70513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70513 prefixEnd_70513 := by exact prefixLift 70513
  have htrace : WordTrace (prefixWord ++ tailWord_70513) baseStart_70513 baseEnd_70513 := by
    simpa [prefixWord, tailWord_70513, baseEnd_70513] using wordTrace_append hprefix tailTrace_70513
  have hstable : (prefixWord ++ tailWord_70513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70513).length < 2 ^ (prefixWord ++ tailWord_70513).sum := by decide
  have hdescent : baseEnd_70513 < baseStart_70513 := by decide
  rcases family_descends (prefixWord ++ tailWord_70513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70549 : List Nat := [1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_70549 : Nat := 118140960795 + 70549 * 2 ^ 59
def prefixEnd_70549 : Nat := 4983230072969 + 3 ^ 40 * 70549 * 2
def baseEnd_70549 : Nat := 21466990633570198763293

theorem tailTrace_70549 : CollatzResearch.WordTrace tailWord_70549 prefixEnd_70549 21466990633570198763293 := by
  unfold tailWord_70549
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573133421420496655054701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1715422280946997770036467 2573133421420496655054701)
  ·
    refine ⟨964925033032686245645513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2573133421420496655054701 964925033032686245645513)
    ·
      refine ⟨723693774774514684234135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 964925033032686245645513 723693774774514684234135)
      ·
        refine ⟨1085540662161772026351203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723693774774514684234135 1085540662161772026351203)
        ·
          refine ⟨1628310993242658039526805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085540662161772026351203 1628310993242658039526805)
          ·
            refine ⟨76327077808249595602819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1628310993242658039526805 76327077808249595602819)
            ·
              refine ⟨114490616712374393404229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76327077808249595602819 114490616712374393404229)
              ·
                refine ⟨21466990633570198763293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114490616712374393404229 21466990633570198763293)
                ·
                  rfl

theorem cell19_70549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_70549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70549 prefixEnd_70549 := by exact prefixLift 70549
  have htrace : WordTrace (prefixWord ++ tailWord_70549) baseStart_70549 baseEnd_70549 := by
    simpa [prefixWord, tailWord_70549, baseEnd_70549] using wordTrace_append hprefix tailTrace_70549
  have hstable : (prefixWord ++ tailWord_70549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70549).length < 2 ^ (prefixWord ++ tailWord_70549).sum := by decide
  have hdescent : baseEnd_70549 < baseStart_70549 := by decide
  rcases family_descends (prefixWord ++ tailWord_70549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70623 : List Nat := [1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_70623 : Nat := 118140960795 + 70623 * 2 ^ 59
def prefixEnd_70623 : Nat := 4983230072969 + 3 ^ 40 * 70623 * 2
def baseEnd_70623 : Nat := 21489507711159953118647

theorem tailTrace_70623 : CollatzResearch.WordTrace tailWord_70623 prefixEnd_70623 21489507711159953118647 := by
  unfold tailWord_70623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575832423152407293248523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1717221615434938195499015 2575832423152407293248523)
  ·
    refine ⟨3863748634728610939872785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2575832423152407293248523 3863748634728610939872785)
    ·
      refine ⟨2897811476046458204904589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3863748634728610939872785 2897811476046458204904589)
      ·
        refine ⟨1086679303517421826839221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2897811476046458204904589 1086679303517421826839221)
        ·
          refine ⟨101876184704758296266177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1086679303517421826839221 101876184704758296266177)
          ·
            refine ⟨76407138528568722199633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101876184704758296266177 76407138528568722199633)
            ·
              refine ⟨57305353896426541649725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76407138528568722199633 57305353896426541649725)
              ·
                refine ⟨21489507711159953118647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57305353896426541649725 21489507711159953118647)
                ·
                  rfl

theorem cell19_70623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_70623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70623 prefixEnd_70623 := by exact prefixLift 70623
  have htrace : WordTrace (prefixWord ++ tailWord_70623) baseStart_70623 baseEnd_70623 := by
    simpa [prefixWord, tailWord_70623, baseEnd_70623] using wordTrace_append hprefix tailTrace_70623
  have hstable : (prefixWord ++ tailWord_70623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70623).length < 2 ^ (prefixWord ++ tailWord_70623).sum := by decide
  have hdescent : baseEnd_70623 < baseStart_70623 := by decide
  rcases family_descends (prefixWord ++ tailWord_70623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70627 : List Nat := [1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_70627 : Nat := 118140960795 + 70627 * 2 ^ 59
def prefixEnd_70627 : Nat := 4983230072969 + 3 ^ 40 * 70627 * 2
def baseEnd_70627 : Nat := 21490724850489129029747

theorem tailTrace_70627 : CollatzResearch.WordTrace tailWord_70627 prefixEnd_70627 21490724850489129029747 := by
  unfold tailWord_70627
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575978315137915976394135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1717318876758610650929423 2575978315137915976394135)
  ·
    refine ⟨3863967472706873964591203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2575978315137915976394135 3863967472706873964591203)
    ·
      refine ⟨5795951209060310946886805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863967472706873964591203 5795951209060310946886805)
      ·
        refine ⟨271685212924702075635319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5795951209060310946886805 271685212924702075635319)
        ·
          refine ⟨407527819387053113452979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271685212924702075635319 407527819387053113452979)
          ·
            refine ⟨611291729080579670179469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407527819387053113452979 611291729080579670179469)
            ·
              refine ⟨229234398405217376317301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611291729080579670179469 229234398405217376317301)
              ·
                refine ⟨21490724850489129029747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229234398405217376317301 21490724850489129029747)
                ·
                  rfl

theorem cell19_70627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_70627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70627 prefixEnd_70627 := by exact prefixLift 70627
  have htrace : WordTrace (prefixWord ++ tailWord_70627) baseStart_70627 baseEnd_70627 := by
    simpa [prefixWord, tailWord_70627, baseEnd_70627] using wordTrace_append hprefix tailTrace_70627
  have hstable : (prefixWord ++ tailWord_70627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70627).length < 2 ^ (prefixWord ++ tailWord_70627).sum := by decide
  have hdescent : baseEnd_70627 < baseStart_70627 := by decide
  rcases family_descends (prefixWord ++ tailWord_70627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70642 : List Nat := [3, 2, 1, 5, 1, 2, 5]
def baseStart_70642 : Nat := 118140960795 + 70642 * 2 ^ 59
def prefixEnd_70642 : Nat := 4983230072969 + 3 ^ 40 * 70642 * 2
def baseEnd_70642 : Nat := 7165096374324512898791

theorem tailTrace_70642 : CollatzResearch.WordTrace tailWord_70642 prefixEnd_70642 7165096374324512898791 := by
  unfold tailWord_70642
  simp only [CollatzResearch.WordTrace]
  refine ⟨644131352520893384547545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1717683606722382358793453 644131352520893384547545)
  ·
    refine ⟨483098514390670038410659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 644131352520893384547545 483098514390670038410659)
    ·
      refine ⟨724647771586005057615989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483098514390670038410659 724647771586005057615989)
      ·
        refine ⟨67935728586187974151499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 724647771586005057615989 67935728586187974151499)
        ·
          refine ⟨101903592879281961227249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67935728586187974151499 101903592879281961227249)
          ·
            refine ⟨76427694659461470920437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101903592879281961227249 76427694659461470920437)
            ·
              refine ⟨7165096374324512898791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76427694659461470920437 7165096374324512898791)
              ·
                rfl

theorem cell19_70642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_70642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70642 prefixEnd_70642 := by exact prefixLift 70642
  have htrace : WordTrace (prefixWord ++ tailWord_70642) baseStart_70642 baseEnd_70642 := by
    simpa [prefixWord, tailWord_70642, baseEnd_70642] using wordTrace_append hprefix tailTrace_70642
  have hstable : (prefixWord ++ tailWord_70642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70642).length < 2 ^ (prefixWord ++ tailWord_70642).sum := by decide
  have hdescent : baseEnd_70642 < baseStart_70642 := by decide
  rcases family_descends (prefixWord ++ tailWord_70642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70718 : List Nat := [4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_70718 : Nat := 118140960795 + 70718 * 2 ^ 59
def prefixEnd_70718 : Nat := 4983230072969 + 3 ^ 40 * 70718 * 2
def baseEnd_70718 : Nat := 21518414770227881007277

theorem tailTrace_70718 : CollatzResearch.WordTrace tailWord_70718 prefixEnd_70718 21518414770227881007277 := by
  unfold tailWord_70718
  simp only [CollatzResearch.WordTrace]
  refine ⟨322412169726029814744601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1719531571872159011971205 322412169726029814744601)
  ·
    refine ⟨241809127294522361058451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 322412169726029814744601 241809127294522361058451)
    ·
      refine ⟨362713690941783541587677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241809127294522361058451 362713690941783541587677)
      ·
        refine ⟨136017634103168828095379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362713690941783541587677 136017634103168828095379)
        ·
          refine ⟨204026451154753242143069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136017634103168828095379 204026451154753242143069)
          ·
            refine ⟨76509919183032465803651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204026451154753242143069 76509919183032465803651)
            ·
              refine ⟨114764878774548698705477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76509919183032465803651 114764878774548698705477)
              ·
                refine ⟨21518414770227881007277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114764878774548698705477 21518414770227881007277)
                ·
                  rfl

theorem cell19_70718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_70718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70718 prefixEnd_70718 := by exact prefixLift 70718
  have htrace : WordTrace (prefixWord ++ tailWord_70718) baseStart_70718 baseEnd_70718 := by
    simpa [prefixWord, tailWord_70718, baseEnd_70718] using wordTrace_append hprefix tailTrace_70718
  have hstable : (prefixWord ++ tailWord_70718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70718).length < 2 ^ (prefixWord ++ tailWord_70718).sum := by decide
  have hdescent : baseEnd_70718 < baseStart_70718 := by decide
  rcases family_descends (prefixWord ++ tailWord_70718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70792 : List Nat := [2, 1, 3, 4, 3, 1, 2, 3]
def baseStart_70792 : Nat := 118140960795 + 70792 * 2 ^ 59
def prefixEnd_70792 : Nat := 4983230072969 + 3 ^ 40 * 70792 * 2
def baseEnd_70792 : Nat := 21540931847817635362631

theorem tailTrace_70792 : CollatzResearch.WordTrace tailWord_70792 prefixEnd_70792 21540931847817635362631 := by
  unfold tailWord_70792
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290998179770074578075315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1721330906360099437433753 1290998179770074578075315)
  ·
    refine ⟨1936497269655111867112973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290998179770074578075315 1936497269655111867112973)
    ·
      refine ⟨726186476120666950167365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1936497269655111867112973 726186476120666950167365)
      ·
        refine ⟨136159964272625053156381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 726186476120666950167365 136159964272625053156381)
        ·
          refine ⟨51059986602234394933643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136159964272625053156381 51059986602234394933643)
          ·
            refine ⟨76589979903351592400465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51059986602234394933643 76589979903351592400465)
            ·
              refine ⟨57442484927513694300349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76589979903351592400465 57442484927513694300349)
              ·
                refine ⟨21540931847817635362631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57442484927513694300349 21540931847817635362631)
                ·
                  rfl

theorem cell19_70792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_70792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70792 prefixEnd_70792 := by exact prefixLift 70792
  have htrace : WordTrace (prefixWord ++ tailWord_70792) baseStart_70792 baseEnd_70792 := by
    simpa [prefixWord, tailWord_70792, baseEnd_70792] using wordTrace_append hprefix tailTrace_70792
  have hstable : (prefixWord ++ tailWord_70792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70792).length < 2 ^ (prefixWord ++ tailWord_70792).sum := by decide
  have hdescent : baseEnd_70792 < baseStart_70792 := by decide
  rcases family_descends (prefixWord ++ tailWord_70792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70815 : List Nat := [1, 1, 2, 6, 2, 2, 5]
def baseStart_70815 : Nat := 118140960795 + 70815 * 2 ^ 59
def prefixEnd_70815 : Nat := 4983230072969 + 3 ^ 40 * 70815 * 2
def baseEnd_70815 : Nat := 7182643466320132283819

theorem tailTrace_70815 : CollatzResearch.WordTrace tailWord_70815 prefixEnd_70815 7182643466320132283819 := by
  unfold tailWord_70815
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582835238456824084237899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1721890158971216056158599 2582835238456824084237899)
  ·
    refine ⟨3874252857685236126356849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2582835238456824084237899 3874252857685236126356849)
    ·
      refine ⟨2905689643263927094767637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3874252857685236126356849 2905689643263927094767637)
      ·
        refine ⟨136204202027996582567233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2905689643263927094767637 136204202027996582567233)
        ·
          refine ⟨102153151520997436925425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136204202027996582567233 102153151520997436925425)
          ·
            refine ⟨76614863640748077694069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102153151520997436925425 76614863640748077694069)
            ·
              refine ⟨7182643466320132283819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76614863640748077694069 7182643466320132283819)
              ·
                rfl

theorem cell19_70815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_70815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70815 prefixEnd_70815 := by exact prefixLift 70815
  have htrace : WordTrace (prefixWord ++ tailWord_70815) baseStart_70815 baseEnd_70815 := by
    simpa [prefixWord, tailWord_70815, baseEnd_70815] using wordTrace_append hprefix tailTrace_70815
  have hstable : (prefixWord ++ tailWord_70815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70815).length < 2 ^ (prefixWord ++ tailWord_70815).sum := by decide
  have hdescent : baseEnd_70815 < baseStart_70815 := by decide
  rcases family_descends (prefixWord ++ tailWord_70815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70870 : List Nat := [5, 2, 1, 2, 3, 6]
def baseStart_70870 : Nat := 118140960795 + 70870 * 2 ^ 59
def prefixEnd_70870 : Nat := 4983230072969 + 3 ^ 40 * 70870 * 2
def baseEnd_70870 : Nat := 2396074007192951736565

theorem tailTrace_70870 : CollatzResearch.WordTrace tailWord_70870 prefixEnd_70870 2396074007192951736565 := by
  unfold tailWord_70870
  simp only [CollatzResearch.WordTrace]
  refine ⟨161552578328598029843129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1723227502171712318326709 161552578328598029843129)
  ·
    refine ⟨121164433746448522382347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161552578328598029843129 121164433746448522382347)
    ·
      refine ⟨181746650619672783573521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121164433746448522382347 181746650619672783573521)
      ·
        refine ⟨136309987964754587680141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181746650619672783573521 136309987964754587680141)
        ·
          refine ⟨51116245486782970380053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136309987964754587680141 51116245486782970380053)
          ·
            refine ⟨2396074007192951736565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51116245486782970380053 2396074007192951736565)
            ·
              rfl

theorem cell19_70870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_70870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70870 prefixEnd_70870 := by exact prefixLift 70870
  have htrace : WordTrace (prefixWord ++ tailWord_70870) baseStart_70870 baseEnd_70870 := by
    simpa [prefixWord, tailWord_70870, baseEnd_70870] using wordTrace_append hprefix tailTrace_70870
  have hstable : (prefixWord ++ tailWord_70870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70870).length < 2 ^ (prefixWord ++ tailWord_70870).sum := by decide
  have hdescent : baseEnd_70870 < baseStart_70870 := by decide
  rcases family_descends (prefixWord ++ tailWord_70870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70982 : List Nat := [6, 1, 1, 3, 1, 2, 5]
def baseStart_70982 : Nat := 118140960795 + 70982 * 2 ^ 59
def prefixEnd_70982 : Nat := 4983230072969 + 3 ^ 40 * 70982 * 2
def baseEnd_70982 : Nat := 7199581988651163713297

theorem tailTrace_70982 : CollatzResearch.WordTrace tailWord_70982 prefixEnd_70982 7199581988651163713297 := by
  unfold tailWord_70982
  simp only [CollatzResearch.WordTrace]
  refine ⟨80903944651619112673975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1725950819234541070378133 80903944651619112673975)
  ·
    refine ⟨121355916977428669010963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80903944651619112673975 121355916977428669010963)
    ·
      refine ⟨182033875466143003516445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121355916977428669010963 182033875466143003516445)
      ·
        refine ⟨68262703299803626318667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182033875466143003516445 68262703299803626318667)
        ·
          refine ⟨102394054949705439478001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68262703299803626318667 102394054949705439478001)
          ·
            refine ⟨76795541212279079608501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102394054949705439478001 76795541212279079608501)
            ·
              refine ⟨7199581988651163713297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76795541212279079608501 7199581988651163713297)
              ·
                rfl

theorem cell19_70982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_70982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70982 prefixEnd_70982 := by exact prefixLift 70982
  have htrace : WordTrace (prefixWord ++ tailWord_70982) baseStart_70982 baseEnd_70982 := by
    simpa [prefixWord, tailWord_70982, baseEnd_70982] using wordTrace_append hprefix tailTrace_70982
  have hstable : (prefixWord ++ tailWord_70982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70982).length < 2 ^ (prefixWord ++ tailWord_70982).sum := by decide
  have hdescent : baseEnd_70982 < baseStart_70982 := by decide
  rcases family_descends (prefixWord ++ tailWord_70982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70988 : List Nat := [2, 2, 1, 3, 2, 4, 5]
def baseStart_70988 : Nat := 118140960795 + 70988 * 2 ^ 59
def prefixEnd_70988 : Nat := 4983230072969 + 3 ^ 40 * 70988 * 2
def baseEnd_70988 : Nat := 7200190558315751668847

theorem tailTrace_70988 : CollatzResearch.WordTrace tailWord_70988 prefixEnd_70988 7200190558315751668847 := by
  unfold tailWord_70988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294572533415037315142809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1726096711220049753523745 1294572533415037315142809)
  ·
    refine ⟨970929400061277986357107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1294572533415037315142809 970929400061277986357107)
    ·
      refine ⟨1456394100091916979535661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970929400061277986357107 1456394100091916979535661)
      ·
        refine ⟨546147787534468867325873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1456394100091916979535661 546147787534468867325873)
        ·
          refine ⟨409610840650851650494405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546147787534468867325873 409610840650851650494405)
          ·
            refine ⟨76802032622034684467701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409610840650851650494405 76802032622034684467701)
            ·
              refine ⟨7200190558315751668847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76802032622034684467701 7200190558315751668847)
              ·
                rfl

theorem cell19_70988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_70988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70988 prefixEnd_70988 := by exact prefixLift 70988
  have htrace : WordTrace (prefixWord ++ tailWord_70988) baseStart_70988 baseEnd_70988 := by
    simpa [prefixWord, tailWord_70988, baseEnd_70988] using wordTrace_append hprefix tailTrace_70988
  have hstable : (prefixWord ++ tailWord_70988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70988).length < 2 ^ (prefixWord ++ tailWord_70988).sum := by decide
  have hdescent : baseEnd_70988 < baseStart_70988 := by decide
  rcases family_descends (prefixWord ++ tailWord_70988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71047 : List Nat := [1, 1, 4, 2, 2, 9]
def baseStart_71047 : Nat := 118140960795 + 71047 * 2 ^ 59
def prefixEnd_71047 : Nat := 4983230072969 + 3 ^ 40 * 71047 * 2
def baseEnd_71047 : Nat := 2402058275561399966141

theorem tailTrace_71047 : CollatzResearch.WordTrace tailWord_71047 prefixEnd_71047 2402058275561399966141 := by
  unfold tailWord_71047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591296973616327706683395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1727531315744218471122263 2591296973616327706683395)
  ·
    refine ⟨3886945460424491560025093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2591296973616327706683395 3886945460424491560025093)
    ·
      refine ⟨728802273829592167504705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3886945460424491560025093 728802273829592167504705)
      ·
        refine ⟨546601705372194125628529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728802273829592167504705 546601705372194125628529)
        ·
          refine ⟨409951279029145594221397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546601705372194125628529 409951279029145594221397)
          ·
            refine ⟨2402058275561399966141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 409951279029145594221397 2402058275561399966141)
            ·
              rfl

theorem cell19_71047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_71047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71047 prefixEnd_71047 := by exact prefixLift 71047
  have htrace : WordTrace (prefixWord ++ tailWord_71047) baseStart_71047 baseEnd_71047 := by
    simpa [prefixWord, tailWord_71047, baseEnd_71047] using wordTrace_append hprefix tailTrace_71047
  have hstable : (prefixWord ++ tailWord_71047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71047).length < 2 ^ (prefixWord ++ tailWord_71047).sum := by decide
  have hdescent : baseEnd_71047 < baseStart_71047 := by decide
  rcases family_descends (prefixWord ++ tailWord_71047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71058 : List Nat := [3, 2, 3, 3, 2, 1, 1, 4]
def baseStart_71058 : Nat := 118140960795 + 71058 * 2 ^ 59
def prefixEnd_71058 : Nat := 4983230072969 + 3 ^ 40 * 71058 * 2
def baseEnd_71058 : Nat := 21621871613207833450795

theorem tailTrace_71058 : CollatzResearch.WordTrace tailWord_71058 prefixEnd_71058 21621871613207833450795 := by
  unfold tailWord_71058
  simp only [CollatzResearch.WordTrace]
  refine ⟨647924544144119146333457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1727798784384317723555885 647924544144119146333457)
  ·
    refine ⟨485943408108089359750093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 647924544144119146333457 485943408108089359750093)
    ·
      refine ⟨182228778040533509906285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 485943408108089359750093 182228778040533509906285)
      ·
        refine ⟨68335791765200066214857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182228778040533509906285 68335791765200066214857)
        ·
          refine ⟨51251843823900049661143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68335791765200066214857 51251843823900049661143)
          ·
            refine ⟨76877765735850074491715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51251843823900049661143 76877765735850074491715)
            ·
              refine ⟨115316648603775111737573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76877765735850074491715 115316648603775111737573)
              ·
                refine ⟨21621871613207833450795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115316648603775111737573 21621871613207833450795)
                ·
                  rfl

theorem cell19_71058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_71058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71058 prefixEnd_71058 := by exact prefixLift 71058
  have htrace : WordTrace (prefixWord ++ tailWord_71058) baseStart_71058 baseEnd_71058 := by
    simpa [prefixWord, tailWord_71058, baseEnd_71058] using wordTrace_append hprefix tailTrace_71058
  have hstable : (prefixWord ++ tailWord_71058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71058).length < 2 ^ (prefixWord ++ tailWord_71058).sum := by decide
  have hdescent : baseEnd_71058 < baseStart_71058 := by decide
  rcases family_descends (prefixWord ++ tailWord_71058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71157 : List Nat := [1, 3, 5, 1, 1, 3, 5]
def baseStart_71157 : Nat := 118140960795 + 71157 * 2 ^ 59
def prefixEnd_71157 : Nat := 4983230072969 + 3 ^ 40 * 71157 * 2
def baseEnd_71157 : Nat := 7217331937201645750175

theorem tailTrace_71157 : CollatzResearch.WordTrace tailWord_71157 prefixEnd_71157 7217331937201645750175 := by
  unfold tailWord_71157
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595309003217816493187725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1730206002145210995458483 2595309003217816493187725)
  ·
    refine ⟨973240876206681184945397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2595309003217816493187725 973240876206681184945397)
    ·
      refine ⟨91241332144376361088631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 973240876206681184945397 91241332144376361088631)
      ·
        refine ⟨136861998216564541632947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91241332144376361088631 136861998216564541632947)
        ·
          refine ⟨205292997324846812449421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136861998216564541632947 205292997324846812449421)
          ·
            refine ⟨76984873996817554668533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205292997324846812449421 76984873996817554668533)
            ·
              refine ⟨7217331937201645750175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76984873996817554668533 7217331937201645750175)
              ·
                rfl

theorem cell19_71157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_71157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71157 prefixEnd_71157 := by exact prefixLift 71157
  have htrace : WordTrace (prefixWord ++ tailWord_71157) baseStart_71157 baseEnd_71157 := by
    simpa [prefixWord, tailWord_71157, baseEnd_71157] using wordTrace_append hprefix tailTrace_71157
  have hstable : (prefixWord ++ tailWord_71157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71157).length < 2 ^ (prefixWord ++ tailWord_71157).sum := by decide
  have hdescent : baseEnd_71157 < baseStart_71157 := by decide
  rcases family_descends (prefixWord ++ tailWord_71157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71178 : List Nat := [3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_71178 : Nat := 118140960795 + 71178 * 2 ^ 59
def prefixEnd_71178 : Nat := 4983230072969 + 3 ^ 40 * 71178 * 2
def baseEnd_71178 : Nat := 21658385793083110783801

theorem tailTrace_71178 : CollatzResearch.WordTrace tailWord_71178 prefixEnd_71178 21658385793083110783801 := by
  unfold tailWord_71178
  simp only [CollatzResearch.WordTrace]
  refine ⟨649018734035434269925547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1730716624094491386468125 649018734035434269925547)
  ·
    refine ⟨973528101053151404888321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649018734035434269925547 973528101053151404888321)
    ·
      refine ⟨730146075789863553666241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 973528101053151404888321 730146075789863553666241)
      ·
        refine ⟨547609556842397665249681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 730146075789863553666241 547609556842397665249681)
        ·
          refine ⟨410707167631798248937261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547609556842397665249681 410707167631798248937261)
          ·
            refine ⟨154015187861924343351473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410707167631798248937261 154015187861924343351473)
            ·
              refine ⟨115511390896443257513605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154015187861924343351473 115511390896443257513605)
              ·
                refine ⟨21658385793083110783801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115511390896443257513605 21658385793083110783801)
                ·
                  rfl

theorem cell19_71178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_71178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71178 prefixEnd_71178 := by exact prefixLift 71178
  have htrace : WordTrace (prefixWord ++ tailWord_71178) baseStart_71178 baseEnd_71178 := by
    simpa [prefixWord, tailWord_71178, baseEnd_71178] using wordTrace_append hprefix tailTrace_71178
  have hstable : (prefixWord ++ tailWord_71178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71178).length < 2 ^ (prefixWord ++ tailWord_71178).sum := by decide
  have hdescent : baseEnd_71178 < baseStart_71178 := by decide
  rcases family_descends (prefixWord ++ tailWord_71178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71199 : List Nat := [1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_71199 : Nat := 118140960795 + 71199 * 2 ^ 59
def prefixEnd_71199 : Nat := 4983230072969 + 3 ^ 40 * 71199 * 2
def baseEnd_71199 : Nat := 21664775774561284317077

theorem tailTrace_71199 : CollatzResearch.WordTrace tailWord_71199 prefixEnd_71199 21664775774561284317077 := by
  unfold tailWord_71199
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596840869065657666216651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1731227246043771777477767 2596840869065657666216651)
  ·
    refine ⟨3895261303598486499324977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2596840869065657666216651 3895261303598486499324977)
    ·
      refine ⟨2921445977698864874493733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895261303598486499324977 2921445977698864874493733)
      ·
        refine ⟨547771120818537163967575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2921445977698864874493733 547771120818537163967575)
        ·
          refine ⟨821656681227805745951363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547771120818537163967575 821656681227805745951363)
          ·
            refine ⟨1232485021841708618927045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821656681227805745951363 1232485021841708618927045)
            ·
              refine ⟨231090941595320366048821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1232485021841708618927045 231090941595320366048821)
              ·
                refine ⟨21664775774561284317077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231090941595320366048821 21664775774561284317077)
                ·
                  rfl

theorem cell19_71199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_71199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71199 prefixEnd_71199 := by exact prefixLift 71199
  have htrace : WordTrace (prefixWord ++ tailWord_71199) baseStart_71199 baseEnd_71199 := by
    simpa [prefixWord, tailWord_71199, baseEnd_71199] using wordTrace_append hprefix tailTrace_71199
  have hstable : (prefixWord ++ tailWord_71199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71199).length < 2 ^ (prefixWord ++ tailWord_71199).sum := by decide
  have hdescent : baseEnd_71199 < baseStart_71199 := by decide
  rcases family_descends (prefixWord ++ tailWord_71199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71332 : List Nat := [2, 3, 1, 2, 2, 2, 7]
def baseStart_71332 : Nat := 118140960795 + 71332 * 2 ^ 59
def prefixEnd_71332 : Nat := 4983230072969 + 3 ^ 40 * 71332 * 2
def baseEnd_71332 : Nat := 7235081885752127787053

theorem tailTrace_71332 : CollatzResearch.WordTrace tailWord_71332 prefixEnd_71332 7235081885752127787053 := by
  unfold tailWord_71332
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300845888791910690404125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1734461185055880920538833 1300845888791910690404125)
  ·
    refine ⟨487817208296966508901547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1300845888791910690404125 487817208296966508901547)
    ·
      refine ⟨731725812445449763352321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487817208296966508901547 731725812445449763352321)
      ·
        refine ⟨548794359334087322514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 731725812445449763352321 548794359334087322514241)
        ·
          refine ⟨411595769500565491885681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548794359334087322514241 411595769500565491885681)
          ·
            refine ⟨308696827125424118914261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411595769500565491885681 308696827125424118914261)
            ·
              refine ⟨7235081885752127787053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 308696827125424118914261 7235081885752127787053)
              ·
                rfl

theorem cell19_71332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_71332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71332 prefixEnd_71332 := by exact prefixLift 71332
  have htrace : WordTrace (prefixWord ++ tailWord_71332) baseStart_71332 baseEnd_71332 := by
    simpa [prefixWord, tailWord_71332, baseEnd_71332] using wordTrace_append hprefix tailTrace_71332
  have hstable : (prefixWord ++ tailWord_71332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71332).length < 2 ^ (prefixWord ++ tailWord_71332).sum := by decide
  have hdescent : baseEnd_71332 < baseStart_71332 := by decide
  rcases family_descends (prefixWord ++ tailWord_71332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71351 : List Nat := [1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_71351 : Nat := 118140960795 + 71351 * 2 ^ 59
def prefixEnd_71351 : Nat := 4983230072969 + 3 ^ 40 * 71351 * 2
def baseEnd_71351 : Nat := 21711027069069968938885

theorem tailTrace_71351 : CollatzResearch.WordTrace tailWord_71351 prefixEnd_71351 21711027069069968938885 := by
  unfold tailWord_71351
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602384764514987625749907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1734923176343325083833271 2602384764514987625749907)
  ·
    refine ⟨3903577146772481438624861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602384764514987625749907 3903577146772481438624861)
    ·
      refine ⟨1463841430039680539484323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3903577146772481438624861 1463841430039680539484323)
      ·
        refine ⟨2195762145059520809226485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463841430039680539484323 2195762145059520809226485)
        ·
          refine ⟨205852701099330075864983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2195762145059520809226485 205852701099330075864983)
          ·
            refine ⟨308779051648995113797475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205852701099330075864983 308779051648995113797475)
            ·
              refine ⟨463168577473492670696213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308779051648995113797475 463168577473492670696213)
              ·
                refine ⟨21711027069069968938885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 463168577473492670696213 21711027069069968938885)
                ·
                  rfl

theorem cell19_71351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_71351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71351 prefixEnd_71351 := by exact prefixLift 71351
  have htrace : WordTrace (prefixWord ++ tailWord_71351) baseStart_71351 baseEnd_71351 := by
    simpa [prefixWord, tailWord_71351, baseEnd_71351] using wordTrace_append hprefix tailTrace_71351
  have hstable : (prefixWord ++ tailWord_71351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71351).length < 2 ^ (prefixWord ++ tailWord_71351).sum := by decide
  have hdescent : baseEnd_71351 < baseStart_71351 := by decide
  rcases family_descends (prefixWord ++ tailWord_71351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71478 : List Nat := [5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_71478 : Nat := 118140960795 + 71478 * 2 ^ 59
def prefixEnd_71478 : Nat := 4983230072969 + 3 ^ 40 * 71478 * 2
def baseEnd_71478 : Nat := 21749671242771304116317

theorem tailTrace_71478 : CollatzResearch.WordTrace tailWord_71478 prefixEnd_71478 21749671242771304116317 := by
  unfold tailWord_71478
  simp only [CollatzResearch.WordTrace]
  refine ⟨162938552190930519726443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1738011223369925543748725 162938552190930519726443)
  ·
    refine ⟨244407828286395779589665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162938552190930519726443 244407828286395779589665)
    ·
      refine ⟨183305871214796834692249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244407828286395779589665 183305871214796834692249)
      ·
        refine ⟨137479403411097626019187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183305871214796834692249 137479403411097626019187)
        ·
          refine ⟨206219105116646439028781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137479403411097626019187 206219105116646439028781)
          ·
            refine ⟨77332164418742414635793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206219105116646439028781 77332164418742414635793)
            ·
              refine ⟨57999123314056810976845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77332164418742414635793 57999123314056810976845)
              ·
                refine ⟨21749671242771304116317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57999123314056810976845 21749671242771304116317)
                ·
                  rfl

theorem cell19_71478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_71478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71478 prefixEnd_71478 := by exact prefixLift 71478
  have htrace : WordTrace (prefixWord ++ tailWord_71478) baseStart_71478 baseEnd_71478 := by
    simpa [prefixWord, tailWord_71478, baseEnd_71478] using wordTrace_append hprefix tailTrace_71478
  have hstable : (prefixWord ++ tailWord_71478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71478).length < 2 ^ (prefixWord ++ tailWord_71478).sum := by decide
  have hdescent : baseEnd_71478 < baseStart_71478 := by decide
  rcases family_descends (prefixWord ++ tailWord_71478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71482 : List Nat := [3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_71482 : Nat := 118140960795 + 71482 * 2 ^ 59
def prefixEnd_71482 : Nat := 4983230072969 + 3 ^ 40 * 71482 * 2
def baseEnd_71482 : Nat := 21750888382100480027417

theorem tailTrace_71482 : CollatzResearch.WordTrace tailWord_71482 prefixEnd_71482 21750888382100480027417 := by
  unfold tailWord_71482
  simp only [CollatzResearch.WordTrace]
  refine ⟨651790681760099249692175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1738108484693597999179133 651790681760099249692175)
  ·
    refine ⟨977686022640148874538263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 651790681760099249692175 977686022640148874538263)
    ·
      refine ⟨1466529033960223311807395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977686022640148874538263 1466529033960223311807395)
      ·
        refine ⟨2199793550940334967711093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466529033960223311807395 2199793550940334967711093)
        ·
          refine ⟨206230645400656403222915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2199793550940334967711093 206230645400656403222915)
          ·
            refine ⟨309345968100984604834373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206230645400656403222915 309345968100984604834373)
            ·
              refine ⟨58002369018934613406445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309345968100984604834373 58002369018934613406445)
              ·
                refine ⟨21750888382100480027417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58002369018934613406445 21750888382100480027417)
                ·
                  rfl

theorem cell19_71482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_71482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71482 prefixEnd_71482 := by exact prefixLift 71482
  have htrace : WordTrace (prefixWord ++ tailWord_71482) baseStart_71482 baseEnd_71482 := by
    simpa [prefixWord, tailWord_71482, baseEnd_71482] using wordTrace_append hprefix tailTrace_71482
  have hstable : (prefixWord ++ tailWord_71482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71482).length < 2 ^ (prefixWord ++ tailWord_71482).sum := by decide
  have hdescent : baseEnd_71482 < baseStart_71482 := by decide
  rcases family_descends (prefixWord ++ tailWord_71482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71501 : List Nat := [1, 6, 1, 2, 1, 1, 7]
def baseStart_71501 : Nat := 118140960795 + 71501 * 2 ^ 59
def prefixEnd_71501 : Nat := 4983230072969 + 3 ^ 40 * 71501 * 2
def baseEnd_71501 : Nat := 7252223264638021868381

theorem tailTrace_71501 : CollatzResearch.WordTrace tailWord_71501 prefixEnd_71501 7252223264638021868381 := by
  unfold tailWord_71501
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607855713971563243710357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1738570475981042162473571 2607855713971563243710357)
  ·
    refine ⟨122243236592417027048923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2607855713971563243710357 122243236592417027048923)
    ·
      refine ⟨183364854888625540573385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122243236592417027048923 183364854888625540573385)
      ·
        refine ⟨137523641166469155430039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183364854888625540573385 137523641166469155430039)
        ·
          refine ⟨206285461749703733145059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137523641166469155430039 206285461749703733145059)
          ·
            refine ⟨309428192624555599717589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206285461749703733145059 309428192624555599717589)
            ·
              refine ⟨7252223264638021868381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 309428192624555599717589 7252223264638021868381)
              ·
                rfl

theorem cell19_71501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_71501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71501 prefixEnd_71501 := by exact prefixLift 71501
  have htrace : WordTrace (prefixWord ++ tailWord_71501) baseStart_71501 baseEnd_71501 := by
    simpa [prefixWord, tailWord_71501, baseEnd_71501] using wordTrace_append hprefix tailTrace_71501
  have hstable : (prefixWord ++ tailWord_71501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71501).length < 2 ^ (prefixWord ++ tailWord_71501).sum := by decide
  have hdescent : baseEnd_71501 < baseStart_71501 := by decide
  rcases family_descends (prefixWord ++ tailWord_71501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71541 : List Nat := [1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_71541 : Nat := 118140960795 + 71541 * 2 ^ 59
def prefixEnd_71541 : Nat := 4983230072969 + 3 ^ 40 * 71541 * 2
def baseEnd_71541 : Nat := 21768841187205824716145

theorem tailTrace_71541 : CollatzResearch.WordTrace tailWord_71541 prefixEnd_71541 21768841187205824716145 := by
  unfold tailWord_71541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609314633826650075166477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1739543089217766716777651 2609314633826650075166477)
  ·
    refine ⟨978492987684993778187429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2609314633826650075166477 978492987684993778187429)
    ·
      refine ⟨183467435190936333410143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 978492987684993778187429 183467435190936333410143)
      ·
        refine ⟨275201152786404500115215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183467435190936333410143 275201152786404500115215)
        ·
          refine ⟨412801729179606750172823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275201152786404500115215 412801729179606750172823)
          ·
            refine ⟨619202593769410125259235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412801729179606750172823 619202593769410125259235)
            ·
              refine ⟨928803890654115187888853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619202593769410125259235 928803890654115187888853)
              ·
                refine ⟨21768841187205824716145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 928803890654115187888853 21768841187205824716145)
                ·
                  rfl

theorem cell19_71541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_71541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71541 prefixEnd_71541 := by exact prefixLift 71541
  have htrace : WordTrace (prefixWord ++ tailWord_71541) baseStart_71541 baseEnd_71541 := by
    simpa [prefixWord, tailWord_71541, baseEnd_71541] using wordTrace_append hprefix tailTrace_71541
  have hstable : (prefixWord ++ tailWord_71541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71541).length < 2 ^ (prefixWord ++ tailWord_71541).sum := by decide
  have hdescent : baseEnd_71541 < baseStart_71541 := by decide
  rcases family_descends (prefixWord ++ tailWord_71541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71560 : List Nat := [2, 1, 3, 3, 3, 7]
def baseStart_71560 : Nat := 118140960795 + 71560 * 2 ^ 59
def prefixEnd_71560 : Nat := 4983230072969 + 3 ^ 40 * 71560 * 2
def baseEnd_71560 : Nat := 2419402511002156699319

theorem tailTrace_71560 : CollatzResearch.WordTrace tailWord_71560 prefixEnd_71560 2419402511002156699319 := by
  unfold tailWord_71560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305003810378908160054067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1740005080505210880072089 1305003810378908160054067)
  ·
    refine ⟨1957505715568362240081101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305003810378908160054067 1957505715568362240081101)
    ·
      refine ⟨734064643338135840030413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1957505715568362240081101 734064643338135840030413)
      ·
        refine ⟨275274241251800940011405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 734064643338135840030413 275274241251800940011405)
        ·
          refine ⟨103227840469425352504277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275274241251800940011405 103227840469425352504277)
          ·
            refine ⟨2419402511002156699319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103227840469425352504277 2419402511002156699319)
            ·
              rfl

theorem cell19_71560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_71560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71560 prefixEnd_71560 := by exact prefixLift 71560
  have htrace : WordTrace (prefixWord ++ tailWord_71560) baseStart_71560 baseEnd_71560 := by
    simpa [prefixWord, tailWord_71560, baseEnd_71560] using wordTrace_append hprefix tailTrace_71560
  have hstable : (prefixWord ++ tailWord_71560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71560).length < 2 ^ (prefixWord ++ tailWord_71560).sum := by decide
  have hdescent : baseEnd_71560 < baseStart_71560 := by decide
  rcases family_descends (prefixWord ++ tailWord_71560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71592 : List Nat := [2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_71592 : Nat := 118140960795 + 71592 * 2 ^ 59
def prefixEnd_71592 : Nat := 4983230072969 + 3 ^ 40 * 71592 * 2
def baseEnd_71592 : Nat := 21784359713652817582673

theorem tailTrace_71592 : CollatzResearch.WordTrace tailWord_71592 prefixEnd_71592 21784359713652817582673 := by
  unfold tailWord_71592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305587378320942892636515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1740783171094590523515353 1305587378320942892636515)
  ·
    refine ⟨1958381067481414338954773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305587378320942892636515 1958381067481414338954773)
    ·
      refine ⟨91799112538191297138505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1958381067481414338954773 91799112538191297138505)
      ·
        refine ⟨68849334403643472853879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91799112538191297138505 68849334403643472853879)
        ·
          refine ⟨103274001605465209280819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68849334403643472853879 103274001605465209280819)
          ·
            refine ⟨154911002408197813921229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103274001605465209280819 154911002408197813921229)
            ·
              refine ⟨58091625903074180220461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154911002408197813921229 58091625903074180220461)
              ·
                refine ⟨21784359713652817582673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58091625903074180220461 21784359713652817582673)
                ·
                  rfl

theorem cell19_71592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_71592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71592 prefixEnd_71592 := by exact prefixLift 71592
  have htrace : WordTrace (prefixWord ++ tailWord_71592) baseStart_71592 baseEnd_71592 := by
    simpa [prefixWord, tailWord_71592, baseEnd_71592] using wordTrace_append hprefix tailTrace_71592
  have hstable : (prefixWord ++ tailWord_71592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71592).length < 2 ^ (prefixWord ++ tailWord_71592).sum := by decide
  have hdescent : baseEnd_71592 < baseStart_71592 := by decide
  rcases family_descends (prefixWord ++ tailWord_71592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71636 : List Nat := [2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_71636 : Nat := 118140960795 + 71636 * 2 ^ 59
def prefixEnd_71636 : Nat := 4983230072969 + 3 ^ 40 * 71636 * 2
def baseEnd_71636 : Nat := 21797748246273752604775

theorem tailTrace_71636 : CollatzResearch.WordTrace tailWord_71636 prefixEnd_71636 21797748246273752604775 := by
  unfold tailWord_71636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306389784241240649937381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1741853045654987533249841 1306389784241240649937381)
  ·
    refine ⟨244948084545232621863259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1306389784241240649937381 244948084545232621863259)
    ·
      refine ⟨367422126817848932794889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244948084545232621863259 367422126817848932794889)
      ·
        refine ⟨275566595113386699596167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367422126817848932794889 275566595113386699596167)
        ·
          refine ⟨413349892670080049394251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275566595113386699596167 413349892670080049394251)
          ·
            refine ⟨620024839005120074091377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413349892670080049394251 620024839005120074091377)
            ·
              refine ⟨465018629253840055568533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620024839005120074091377 465018629253840055568533)
              ·
                refine ⟨21797748246273752604775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 465018629253840055568533 21797748246273752604775)
                ·
                  rfl

theorem cell19_71636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_71636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71636 prefixEnd_71636 := by exact prefixLift 71636
  have htrace : WordTrace (prefixWord ++ tailWord_71636) baseStart_71636 baseEnd_71636 := by
    simpa [prefixWord, tailWord_71636, baseEnd_71636] using wordTrace_append hprefix tailTrace_71636
  have hstable : (prefixWord ++ tailWord_71636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71636).length < 2 ^ (prefixWord ++ tailWord_71636).sum := by decide
  have hdescent : baseEnd_71636 < baseStart_71636 := by decide
  rcases family_descends (prefixWord ++ tailWord_71636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71670 : List Nat := [5, 1, 1, 1, 5, 1, 5]
def baseStart_71670 : Nat := 118140960795 + 71670 * 2 ^ 59
def prefixEnd_71670 : Nat := 4983230072969 + 3 ^ 40 * 71670 * 2
def baseEnd_71670 : Nat := 7269364643523915949709

theorem tailTrace_71670 : CollatzResearch.WordTrace tailWord_71670 prefixEnd_71670 7269364643523915949709 := by
  unfold tailWord_71670
  simp only [CollatzResearch.WordTrace]
  refine ⟨163376228147456569163279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1742679766906203404408309 163376228147456569163279)
  ·
    refine ⟨245064342221184853744919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163376228147456569163279 245064342221184853744919)
    ·
      refine ⟨367596513331777280617379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245064342221184853744919 367596513331777280617379)
      ·
        refine ⟨551394769997665920926069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367596513331777280617379 551394769997665920926069)
        ·
          refine ⟨51693259687281180086819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 551394769997665920926069 51693259687281180086819)
          ·
            refine ⟨77539889530921770130229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51693259687281180086819 77539889530921770130229)
            ·
              refine ⟨7269364643523915949709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77539889530921770130229 7269364643523915949709)
              ·
                rfl

theorem cell19_71670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_71670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71670 prefixEnd_71670 := by exact prefixLift 71670
  have htrace : WordTrace (prefixWord ++ tailWord_71670) baseStart_71670 baseEnd_71670 := by
    simpa [prefixWord, tailWord_71670, baseEnd_71670] using wordTrace_append hprefix tailTrace_71670
  have hstable : (prefixWord ++ tailWord_71670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71670).length < 2 ^ (prefixWord ++ tailWord_71670).sum := by decide
  have hdescent : baseEnd_71670 < baseStart_71670 := by decide
  rcases family_descends (prefixWord ++ tailWord_71670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71752 : List Nat := [2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_71752 : Nat := 118140960795 + 71752 * 2 ^ 59
def prefixEnd_71752 : Nat := 4983230072969 + 3 ^ 40 * 71752 * 2
def baseEnd_71752 : Nat := 21833045286819854026681

theorem tailTrace_71752 : CollatzResearch.WordTrace tailWord_71752 prefixEnd_71752 21833045286819854026681 := by
  unfold tailWord_71752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308505218031116555548755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1744673624041488740731673 1308505218031116555548755)
  ·
    refine ⟨1962757827046674833323133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1308505218031116555548755 1962757827046674833323133)
    ·
      refine ⟨736034185142503062496175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1962757827046674833323133 736034185142503062496175)
      ·
        refine ⟨1104051277713754593744263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736034185142503062496175 1104051277713754593744263)
        ·
          refine ⟨1656076916570631890616395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104051277713754593744263 1656076916570631890616395)
          ·
            refine ⟨2484115374855947835924593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656076916570631890616395 2484115374855947835924593)
            ·
              refine ⟨1863086531141960876943445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484115374855947835924593 1863086531141960876943445)
              ·
                refine ⟨21833045286819854026681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1863086531141960876943445 21833045286819854026681)
                ·
                  rfl

theorem cell19_71752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_71752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71752 prefixEnd_71752 := by exact prefixLift 71752
  have htrace : WordTrace (prefixWord ++ tailWord_71752) baseStart_71752 baseEnd_71752 := by
    simpa [prefixWord, tailWord_71752, baseEnd_71752] using wordTrace_append hprefix tailTrace_71752
  have hstable : (prefixWord ++ tailWord_71752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71752).length < 2 ^ (prefixWord ++ tailWord_71752).sum := by decide
  have hdescent : baseEnd_71752 < baseStart_71752 := by decide
  rcases family_descends (prefixWord ++ tailWord_71752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71769 : List Nat := [1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_71769 : Nat := 118140960795 + 71769 * 2 ^ 59
def prefixEnd_71769 : Nat := 4983230072969 + 3 ^ 40 * 71769 * 2
def baseEnd_71769 : Nat := 21838218128968851648857

theorem tailTrace_71769 : CollatzResearch.WordTrace tailWord_71769 prefixEnd_71769 21838218128968851648857 := by
  unfold tailWord_71769
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617630477000645014466361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1745086984667096676310907 2617630477000645014466361)
  ·
    refine ⟨1963222857750483760849771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2617630477000645014466361 1963222857750483760849771)
    ·
      refine ⟨2944834286625725641274657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963222857750483760849771 2944834286625725641274657)
      ·
        refine ⟨2208625714969294230955993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2944834286625725641274657 2208625714969294230955993)
        ·
          refine ⟨1656469286226970673216995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2208625714969294230955993 1656469286226970673216995)
          ·
            refine ⟨2484703929340456009825493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656469286226970673216995 2484703929340456009825493)
            ·
              refine ⟨58235248343916937730285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2484703929340456009825493 58235248343916937730285)
              ·
                refine ⟨21838218128968851648857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58235248343916937730285 21838218128968851648857)
                ·
                  rfl

theorem cell19_71769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_71769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71769 prefixEnd_71769 := by exact prefixLift 71769
  have htrace : WordTrace (prefixWord ++ tailWord_71769) baseStart_71769 baseEnd_71769 := by
    simpa [prefixWord, tailWord_71769, baseEnd_71769] using wordTrace_append hprefix tailTrace_71769
  have hstable : (prefixWord ++ tailWord_71769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71769).length < 2 ^ (prefixWord ++ tailWord_71769).sum := by decide
  have hdescent : baseEnd_71769 < baseStart_71769 := by decide
  rcases family_descends (prefixWord ++ tailWord_71769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71822 : List Nat := [4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_71822 : Nat := 118140960795 + 71822 * 2 ^ 59
def prefixEnd_71822 : Nat := 4983230072969 + 3 ^ 40 * 71822 * 2
def baseEnd_71822 : Nat := 21854345225080432470935

theorem tailTrace_71822 : CollatzResearch.WordTrace tailWord_71822 prefixEnd_71822 21854345225080432470935 := by
  unfold tailWord_71822
  simp only [CollatzResearch.WordTrace]
  refine ⟨327445443226079383268215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1746375697205756710763813 327445443226079383268215)
  ·
    refine ⟨491168164839119074902323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 327445443226079383268215 491168164839119074902323)
    ·
      refine ⟨736752247258678612353485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491168164839119074902323 736752247258678612353485)
      ·
        refine ⟨276282092722004479632557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 736752247258678612353485 276282092722004479632557)
        ·
          refine ⟨103605784770751679862209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276282092722004479632557 103605784770751679862209)
          ·
            refine ⟨77704338578063759896657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103605784770751679862209 77704338578063759896657)
            ·
              refine ⟨58278253933547819922493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77704338578063759896657 58278253933547819922493)
              ·
                refine ⟨21854345225080432470935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58278253933547819922493 21854345225080432470935)
                ·
                  rfl

theorem cell19_71822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_71822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71822 prefixEnd_71822 := by exact prefixLift 71822
  have htrace : WordTrace (prefixWord ++ tailWord_71822) baseStart_71822 baseEnd_71822 := by
    simpa [prefixWord, tailWord_71822, baseEnd_71822] using wordTrace_append hprefix tailTrace_71822
  have hstable : (prefixWord ++ tailWord_71822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71822).length < 2 ^ (prefixWord ++ tailWord_71822).sum := by decide
  have hdescent : baseEnd_71822 < baseStart_71822 := by decide
  rcases family_descends (prefixWord ++ tailWord_71822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71826 : List Nat := [3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_71826 : Nat := 118140960795 + 71826 * 2 ^ 59
def prefixEnd_71826 : Nat := 4983230072969 + 3 ^ 40 * 71826 * 2
def baseEnd_71826 : Nat := 21855562364409608382035

theorem tailTrace_71826 : CollatzResearch.WordTrace tailWord_71826 prefixEnd_71826 21855562364409608382035 := by
  unfold tailWord_71826
  simp only [CollatzResearch.WordTrace]
  refine ⟨654927359448535937322833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1746472958529429166194221 654927359448535937322833)
  ·
    refine ⟨491195519586401952992125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 654927359448535937322833 491195519586401952992125)
    ·
      refine ⟨184198319844900732372047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 491195519586401952992125 184198319844900732372047)
      ·
        refine ⟨276297479767351098558071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184198319844900732372047 276297479767351098558071)
        ·
          refine ⟨414446219651026647837107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276297479767351098558071 414446219651026647837107)
          ·
            refine ⟨621669329476539971755661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414446219651026647837107 621669329476539971755661)
            ·
              refine ⟨233125998553702489408373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 621669329476539971755661 233125998553702489408373)
              ·
                refine ⟨21855562364409608382035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233125998553702489408373 21855562364409608382035)
                ·
                  rfl

theorem cell19_71826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_71826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71826 prefixEnd_71826 := by exact prefixLift 71826
  have htrace : WordTrace (prefixWord ++ tailWord_71826) baseStart_71826 baseEnd_71826 := by
    simpa [prefixWord, tailWord_71826, baseEnd_71826] using wordTrace_append hprefix tailTrace_71826
  have hstable : (prefixWord ++ tailWord_71826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71826).length < 2 ^ (prefixWord ++ tailWord_71826).sum := by decide
  have hdescent : baseEnd_71826 < baseStart_71826 := by decide
  rcases family_descends (prefixWord ++ tailWord_71826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71866 : List Nat := [3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_71866 : Nat := 118140960795 + 71866 * 2 ^ 59
def prefixEnd_71866 : Nat := 4983230072969 + 3 ^ 40 * 71866 * 2
def baseEnd_71866 : Nat := 21867733757701367493037

theorem tailTrace_71866 : CollatzResearch.WordTrace tailWord_71866 prefixEnd_71866 21867733757701367493037 := by
  unfold tailWord_71866
  simp only [CollatzResearch.WordTrace]
  refine ⟨655292089412307645186863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1747445571766153720498301 655292089412307645186863)
  ·
    refine ⟨982938134118461467780295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655292089412307645186863 982938134118461467780295)
    ·
      refine ⟨1474407201177692201670443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982938134118461467780295 1474407201177692201670443)
      ·
        refine ⟨2211610801766538302505665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474407201177692201670443 2211610801766538302505665)
        ·
          refine ⟨1658708101324903726879249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211610801766538302505665 1658708101324903726879249)
          ·
            refine ⟨1244031075993677795159437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1658708101324903726879249 1244031075993677795159437)
            ·
              refine ⟨466511653497629173184789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1244031075993677795159437 466511653497629173184789)
              ·
                refine ⟨21867733757701367493037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 466511653497629173184789 21867733757701367493037)
                ·
                  rfl

theorem cell19_71866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_71866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71866 prefixEnd_71866 := by exact prefixLift 71866
  have htrace : WordTrace (prefixWord ++ tailWord_71866) baseStart_71866 baseEnd_71866 := by
    simpa [prefixWord, tailWord_71866, baseEnd_71866] using wordTrace_append hprefix tailTrace_71866
  have hstable : (prefixWord ++ tailWord_71866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71866).length < 2 ^ (prefixWord ++ tailWord_71866).sum := by decide
  have hdescent : baseEnd_71866 < baseStart_71866 := by decide
  rcases family_descends (prefixWord ++ tailWord_71866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71900 : List Nat := [2, 2, 5, 2, 1, 7]
def baseStart_71900 : Nat := 118140960795 + 71900 * 2 ^ 59
def prefixEnd_71900 : Nat := 4983230072969 + 3 ^ 40 * 71900 * 2
def baseEnd_71900 : Nat := 2430897715777706970821

theorem tailTrace_71900 : CollatzResearch.WordTrace tailWord_71900 prefixEnd_71900 2430897715777706970821 := by
  unfold tailWord_71900
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311204219763027193742577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1748272293017369591656769 1311204219763027193742577)
  ·
    refine ⟨983403164822270395306933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1311204219763027193742577 983403164822270395306933)
    ·
      refine ⟨92194046702087849560025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 983403164822270395306933 92194046702087849560025)
      ·
        refine ⟨69145535026565887170019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92194046702087849560025 69145535026565887170019)
        ·
          refine ⟨103718302539848830755029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69145535026565887170019 103718302539848830755029)
          ·
            refine ⟨2430897715777706970821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103718302539848830755029 2430897715777706970821)
            ·
              rfl

theorem cell19_71900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_71900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71900 prefixEnd_71900 := by exact prefixLift 71900
  have htrace : WordTrace (prefixWord ++ tailWord_71900) baseStart_71900 baseEnd_71900 := by
    simpa [prefixWord, tailWord_71900, baseEnd_71900] using wordTrace_append hprefix tailTrace_71900
  have hstable : (prefixWord ++ tailWord_71900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71900).length < 2 ^ (prefixWord ++ tailWord_71900).sum := by decide
  have hdescent : baseEnd_71900 < baseStart_71900 := by decide
  rcases family_descends (prefixWord ++ tailWord_71900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71917 : List Nat := [1, 5, 1, 2, 4, 1, 1, 4]
def baseStart_71917 : Nat := 118140960795 + 71917 * 2 ^ 59
def prefixEnd_71917 : Nat := 4983230072969 + 3 ^ 40 * 71917 * 2
def baseEnd_71917 : Nat := 21883252284148360359565

theorem tailTrace_71917 : CollatzResearch.WordTrace tailWord_71917 prefixEnd_71917 21883252284148360359565 := by
  unfold tailWord_71917
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623028480464466290854005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1748685653642977527236003 2623028480464466290854005)
  ·
    refine ⟨245908920043543714767563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2623028480464466290854005 245908920043543714767563)
    ·
      refine ⟨368863380065315572151345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245908920043543714767563 368863380065315572151345)
      ·
        refine ⟨276647535048986679113509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368863380065315572151345 276647535048986679113509)
        ·
          refine ⟨51871412821685002333783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276647535048986679113509 51871412821685002333783)
          ·
            refine ⟨77807119232527503500675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51871412821685002333783 77807119232527503500675)
            ·
              refine ⟨116710678848791255251013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77807119232527503500675 116710678848791255251013)
              ·
                refine ⟨21883252284148360359565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116710678848791255251013 21883252284148360359565)
                ·
                  rfl

theorem cell19_71917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_71917 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71917 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71917 prefixEnd_71917 := by exact prefixLift 71917
  have htrace : WordTrace (prefixWord ++ tailWord_71917) baseStart_71917 baseEnd_71917 := by
    simpa [prefixWord, tailWord_71917, baseEnd_71917] using wordTrace_append hprefix tailTrace_71917
  have hstable : (prefixWord ++ tailWord_71917).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71917).length < 2 ^ (prefixWord ++ tailWord_71917).sum := by decide
  have hdescent : baseEnd_71917 < baseStart_71917 := by decide
  rcases family_descends (prefixWord ++ tailWord_71917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71999 : List Nat := [1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_71999 : Nat := 118140960795 + 71999 * 2 ^ 59
def prefixEnd_71999 : Nat := 4983230072969 + 3 ^ 40 * 71999 * 2
def baseEnd_71999 : Nat := 21908203640396466537119

theorem tailTrace_71999 : CollatzResearch.WordTrace tailWord_71999 prefixEnd_71999 21908203640396466537119 := by
  unfold tailWord_71999
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626019266167394295339051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1750679510778262863559367 2626019266167394295339051)
  ·
    refine ⟨3939028899251091443008577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626019266167394295339051 3939028899251091443008577)
    ·
      refine ⟨2954271674438318582256433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3939028899251091443008577 2954271674438318582256433)
      ·
        refine ⟨2215703755828738936692325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2954271674438318582256433 2215703755828738936692325)
        ·
          refine ⟨415444454217888550629811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2215703755828738936692325 415444454217888550629811)
          ·
            refine ⟨623166681326832825944717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415444454217888550629811 623166681326832825944717)
            ·
              refine ⟨233687505497562309729269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623166681326832825944717 233687505497562309729269)
              ·
                refine ⟨21908203640396466537119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233687505497562309729269 21908203640396466537119)
                ·
                  rfl

theorem cell19_71999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_71999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_71999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_71999 prefixEnd_71999 := by exact prefixLift 71999
  have htrace : WordTrace (prefixWord ++ tailWord_71999) baseStart_71999 baseEnd_71999 := by
    simpa [prefixWord, tailWord_71999, baseEnd_71999] using wordTrace_append hprefix tailTrace_71999
  have hstable : (prefixWord ++ tailWord_71999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71999).length < 2 ^ (prefixWord ++ tailWord_71999).sum := by decide
  have hdescent : baseEnd_71999 < baseStart_71999 := by decide
  rcases family_descends (prefixWord ++ tailWord_71999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72018 : List Nat := [3, 2, 2, 1, 1, 1, 9]
def baseStart_72018 : Nat := 118140960795 + 72018 * 2 ^ 59
def prefixEnd_72018 : Nat := 4983230072969 + 3 ^ 40 * 72018 * 2
def baseEnd_72018 : Nat := 7304661684070017371615

theorem tailTrace_72018 : CollatzResearch.WordTrace tailWord_72018 prefixEnd_72018 7304661684070017371615 := by
  unfold tailWord_72018
  simp only [CollatzResearch.WordTrace]
  refine ⟨656678063274640135070177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1751141502065707026853805 656678063274640135070177)
  ·
    refine ⟨492508547455980101302633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 656678063274640135070177 492508547455980101302633)
    ·
      refine ⟨369381410591985075976975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 492508547455980101302633 369381410591985075976975)
      ·
        refine ⟨554072115887977613965463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369381410591985075976975 554072115887977613965463)
        ·
          refine ⟨831108173831966420948195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554072115887977613965463 831108173831966420948195)
          ·
            refine ⟨1246662260747949631422293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831108173831966420948195 1246662260747949631422293)
            ·
              refine ⟨7304661684070017371615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1246662260747949631422293 7304661684070017371615)
              ·
                rfl

theorem cell19_72018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_72018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72018 prefixEnd_72018 := by exact prefixLift 72018
  have htrace : WordTrace (prefixWord ++ tailWord_72018) baseStart_72018 baseEnd_72018 := by
    simpa [prefixWord, tailWord_72018, baseEnd_72018] using wordTrace_append hprefix tailTrace_72018
  have hstable : (prefixWord ++ tailWord_72018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72018).length < 2 ^ (prefixWord ++ tailWord_72018).sum := by decide
  have hdescent : baseEnd_72018 < baseStart_72018 := by decide
  rcases family_descends (prefixWord ++ tailWord_72018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72037 : List Nat := [1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_72037 : Nat := 118140960795 + 72037 * 2 ^ 59
def prefixEnd_72037 : Nat := 4983230072969 + 3 ^ 40 * 72037 * 2
def baseEnd_72037 : Nat := 21919766464023637692571

theorem tailTrace_72037 : CollatzResearch.WordTrace tailWord_72037 prefixEnd_72037 21919766464023637692571 := by
  unfold tailWord_72037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627405240029726785222365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1751603493353151190148243 2627405240029726785222365)
  ·
    refine ⟨985276965011147544458387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2627405240029726785222365 985276965011147544458387)
    ·
      refine ⟨1477915447516721316687581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985276965011147544458387 1477915447516721316687581)
      ·
        refine ⟨554218292818770493757843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1477915447516721316687581 554218292818770493757843)
        ·
          refine ⟨831327439228155740636765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554218292818770493757843 831327439228155740636765)
          ·
            refine ⟨311747789710558402738787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 831327439228155740636765 311747789710558402738787)
            ·
              refine ⟨467621684565837604108181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311747789710558402738787 467621684565837604108181)
              ·
                refine ⟨21919766464023637692571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 467621684565837604108181 21919766464023637692571)
                ·
                  rfl

theorem cell19_72037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_72037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72037 prefixEnd_72037 := by exact prefixLift 72037
  have htrace : WordTrace (prefixWord ++ tailWord_72037) baseStart_72037 baseEnd_72037 := by
    simpa [prefixWord, tailWord_72037, baseEnd_72037] using wordTrace_append hprefix tailTrace_72037
  have hstable : (prefixWord ++ tailWord_72037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72037).length < 2 ^ (prefixWord ++ tailWord_72037).sum := by decide
  have hdescent : baseEnd_72037 < baseStart_72037 := by decide
  rcases family_descends (prefixWord ++ tailWord_72037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72162 : List Nat := [3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_72162 : Nat := 118140960795 + 72162 * 2 ^ 59
def prefixEnd_72162 : Nat := 4983230072969 + 3 ^ 40 * 72162 * 2
def baseEnd_72162 : Nat := 21957802068060384914453

theorem tailTrace_72162 : CollatzResearch.WordTrace tailWord_72162 prefixEnd_72162 21957802068060384914453 := by
  unfold tailWord_72162
  simp only [CollatzResearch.WordTrace]
  refine ⟨657991091144218283380685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1754642909717915422348493 657991091144218283380685)
  ·
    refine ⟨246746659179081856267757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 657991091144218283380685 246746659179081856267757)
    ·
      refine ⟨92529997192155696100409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246746659179081856267757 92529997192155696100409)
      ·
        refine ⟨69397497894116772075307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92529997192155696100409 69397497894116772075307)
        ·
          refine ⟨104096246841175158112961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69397497894116772075307 104096246841175158112961)
          ·
            refine ⟨78072185130881368584721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104096246841175158112961 78072185130881368584721)
            ·
              refine ⟨58554138848161026438541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78072185130881368584721 58554138848161026438541)
              ·
                refine ⟨21957802068060384914453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58554138848161026438541 21957802068060384914453)
                ·
                  rfl

theorem cell19_72162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_72162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72162 prefixEnd_72162 := by exact prefixLift 72162
  have htrace : WordTrace (prefixWord ++ tailWord_72162) baseStart_72162 baseEnd_72162 := by
    simpa [prefixWord, tailWord_72162, baseEnd_72162] using wordTrace_append hprefix tailTrace_72162
  have hstable : (prefixWord ++ tailWord_72162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72162).length < 2 ^ (prefixWord ++ tailWord_72162).sum := by decide
  have hdescent : baseEnd_72162 < baseStart_72162 := by decide
  rcases family_descends (prefixWord ++ tailWord_72162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72168 : List Nat := [2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_72168 : Nat := 118140960795 + 72168 * 2 ^ 59
def prefixEnd_72168 : Nat := 4983230072969 + 3 ^ 40 * 72168 * 2
def baseEnd_72168 : Nat := 21959627777054148781103

theorem tailTrace_72168 : CollatzResearch.WordTrace tailWord_72168 prefixEnd_72168 21959627777054148781103 := by
  unfold tailWord_72168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316091601277568079120579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1754788801703424105494105 1316091601277568079120579)
  ·
    refine ⟨1974137401916352118680869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316091601277568079120579 1974137401916352118680869)
    ·
      refine ⟨370150762859316022252663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1974137401916352118680869 370150762859316022252663)
      ·
        refine ⟨555226144288974033378995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370150762859316022252663 555226144288974033378995)
        ·
          refine ⟨832839216433461050068493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555226144288974033378995 832839216433461050068493)
          ·
            refine ⟨312314706162547893775685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 832839216433461050068493 312314706162547893775685)
            ·
              refine ⟨58559007405477730082941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312314706162547893775685 58559007405477730082941)
              ·
                refine ⟨21959627777054148781103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58559007405477730082941 21959627777054148781103)
                ·
                  rfl

theorem cell19_72168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_72168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72168 prefixEnd_72168 := by exact prefixLift 72168
  have htrace : WordTrace (prefixWord ++ tailWord_72168) baseStart_72168 baseEnd_72168 := by
    simpa [prefixWord, tailWord_72168, baseEnd_72168] using wordTrace_append hprefix tailTrace_72168
  have hstable : (prefixWord ++ tailWord_72168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72168).length < 2 ^ (prefixWord ++ tailWord_72168).sum := by decide
  have hdescent : baseEnd_72168 < baseStart_72168 := by decide
  rcases family_descends (prefixWord ++ tailWord_72168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72206 : List Nat := [4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_72206 : Nat := 118140960795 + 72206 * 2 ^ 59
def prefixEnd_72206 : Nat := 4983230072969 + 3 ^ 40 * 72206 * 2
def baseEnd_72206 : Nat := 21971190600681319936555

theorem tailTrace_72206 : CollatzResearch.WordTrace tailWord_72206 prefixEnd_72206 21971190600681319936555 := by
  unfold tailWord_72206
  simp only [CollatzResearch.WordTrace]
  refine ⟨329196147052183581015559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1755712784278312432082981 329196147052183581015559)
  ·
    refine ⟨493794220578275371523339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329196147052183581015559 493794220578275371523339)
    ·
      refine ⟨740691330867413057285009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493794220578275371523339 740691330867413057285009)
      ·
        refine ⟨555518498150559792963757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 740691330867413057285009 555518498150559792963757)
        ·
          refine ⟨208319436806459922361409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 555518498150559792963757 208319436806459922361409)
          ·
            refine ⟨156239577604844941771057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208319436806459922361409 156239577604844941771057)
            ·
              refine ⟨117179683203633706328293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156239577604844941771057 117179683203633706328293)
              ·
                refine ⟨21971190600681319936555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117179683203633706328293 21971190600681319936555)
                ·
                  rfl

theorem cell19_72206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_72206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72206 prefixEnd_72206 := by exact prefixLift 72206
  have htrace : WordTrace (prefixWord ++ tailWord_72206) baseStart_72206 baseEnd_72206 := by
    simpa [prefixWord, tailWord_72206, baseEnd_72206] using wordTrace_append hprefix tailTrace_72206
  have hstable : (prefixWord ++ tailWord_72206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72206).length < 2 ^ (prefixWord ++ tailWord_72206).sum := by decide
  have hdescent : baseEnd_72206 < baseStart_72206 := by decide
  rcases family_descends (prefixWord ++ tailWord_72206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72227 : List Nat := [1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_72227 : Nat := 118140960795 + 72227 * 2 ^ 59
def prefixEnd_72227 : Nat := 4983230072969 + 3 ^ 40 * 72227 * 2
def baseEnd_72227 : Nat := 21977580582159493469831

theorem tailTrace_72227 : CollatzResearch.WordTrace tailWord_72227 prefixEnd_72227 21977580582159493469831 := by
  unfold tailWord_72227
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634335109341389234638935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1756223406227592823092623 2634335109341389234638935)
  ·
    refine ⟨3951502664012083851958403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2634335109341389234638935 3951502664012083851958403)
    ·
      refine ⟨5927253996018125777937605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3951502664012083851958403 5927253996018125777937605)
      ·
        refine ⟨1111360124253398583363301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5927253996018125777937605 1111360124253398583363301)
        ·
          refine ⟨208380023297512234380619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1111360124253398583363301 208380023297512234380619)
          ·
            refine ⟨312570034946268351570929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208380023297512234380619 312570034946268351570929)
            ·
              refine ⟨234427526209701263678197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312570034946268351570929 234427526209701263678197)
              ·
                refine ⟨21977580582159493469831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234427526209701263678197 21977580582159493469831)
                ·
                  rfl

theorem cell19_72227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_72227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72227 prefixEnd_72227 := by exact prefixLift 72227
  have htrace : WordTrace (prefixWord ++ tailWord_72227) baseStart_72227 baseEnd_72227 := by
    simpa [prefixWord, tailWord_72227, baseEnd_72227] using wordTrace_append hprefix tailTrace_72227
  have hstable : (prefixWord ++ tailWord_72227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72227).length < 2 ^ (prefixWord ++ tailWord_72227).sum := by decide
  have hdescent : baseEnd_72227 < baseStart_72227 := by decide
  rcases family_descends (prefixWord ++ tailWord_72227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72244 : List Nat := [2, 5, 1, 3, 8]
def baseStart_72244 : Nat := 118140960795 + 72244 * 2 ^ 59
def prefixEnd_72244 : Nat := 4983230072969 + 3 ^ 40 * 72244 * 2
def baseEnd_72244 : Nat := 814176052752166336741

theorem tailTrace_72244 : CollatzResearch.WordTrace tailWord_72244 prefixEnd_72244 814176052752166336741 := by
  unfold tailWord_72244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317477575139900569003893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1756636766853200758671857 1317477575139900569003893)
  ·
    refine ⟨123513522669365678344115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1317477575139900569003893 123513522669365678344115)
    ·
      refine ⟨185270284004048517516173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123513522669365678344115 185270284004048517516173)
      ·
        refine ⟨69476356501518194068565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185270284004048517516173 69476356501518194068565)
        ·
          refine ⟨814176052752166336741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 69476356501518194068565 814176052752166336741)
          ·
            rfl

theorem cell19_72244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 8].length) (baseStart_72244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72244 prefixEnd_72244 := by exact prefixLift 72244
  have htrace : WordTrace (prefixWord ++ tailWord_72244) baseStart_72244 baseEnd_72244 := by
    simpa [prefixWord, tailWord_72244, baseEnd_72244] using wordTrace_append hprefix tailTrace_72244
  have hstable : (prefixWord ++ tailWord_72244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72244).length < 2 ^ (prefixWord ++ tailWord_72244).sum := by decide
  have hdescent : baseEnd_72244 < baseStart_72244 := by decide
  rcases family_descends (prefixWord ++ tailWord_72244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72263 : List Nat := [1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_72263 : Nat := 118140960795 + 72263 * 2 ^ 59
def prefixEnd_72263 : Nat := 4983230072969 + 3 ^ 40 * 72263 * 2
def baseEnd_72263 : Nat := 21988534836122076669733

theorem tailTrace_72263 : CollatzResearch.WordTrace tailWord_72263 prefixEnd_72263 21988534836122076669733 := by
  unfold tailWord_72263
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635648137210967382949443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1757098758140644921966295 2635648137210967382949443)
  ·
    refine ⟨3953472205816451074424165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635648137210967382949443 3953472205816451074424165)
    ·
      refine ⟨741276038590584576454531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3953472205816451074424165 741276038590584576454531)
      ·
        refine ⟨1111914057885876864681797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741276038590584576454531 1111914057885876864681797)
        ·
          refine ⟨208483885853601912127837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1111914057885876864681797 208483885853601912127837)
          ·
            refine ⟨78181457195100717047939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208483885853601912127837 78181457195100717047939)
            ·
              refine ⟨117272185792651075571909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78181457195100717047939 117272185792651075571909)
              ·
                refine ⟨21988534836122076669733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117272185792651075571909 21988534836122076669733)
                ·
                  rfl

theorem cell19_72263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_72263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72263 prefixEnd_72263 := by exact prefixLift 72263
  have htrace : WordTrace (prefixWord ++ tailWord_72263) baseStart_72263 baseEnd_72263 := by
    simpa [prefixWord, tailWord_72263, baseEnd_72263] using wordTrace_append hprefix tailTrace_72263
  have hstable : (prefixWord ++ tailWord_72263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72263).length < 2 ^ (prefixWord ++ tailWord_72263).sum := by decide
  have hdescent : baseEnd_72263 < baseStart_72263 := by decide
  rcases family_descends (prefixWord ++ tailWord_72263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72398 : List Nat := [4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_72398 : Nat := 118140960795 + 72398 * 2 ^ 59
def prefixEnd_72398 : Nat := 4983230072969 + 3 ^ 40 * 72398 * 2
def baseEnd_72398 : Nat := 22029613288481763669365

theorem tailTrace_72398 : CollatzResearch.WordTrace tailWord_72398 prefixEnd_72398 22029613288481763669365 := by
  unfold tailWord_72398
  simp only [CollatzResearch.WordTrace]
  refine ⟨330071498965235679889231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1760381327814590292742565 330071498965235679889231)
  ·
    refine ⟨495107248447853519833847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 330071498965235679889231 495107248447853519833847)
    ·
      refine ⟨742660872671780279750771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495107248447853519833847 742660872671780279750771)
      ·
        refine ⟨1113991309007670419626157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742660872671780279750771 1113991309007670419626157)
        ·
          refine ⟨417746740877876407359809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1113991309007670419626157 417746740877876407359809)
          ·
            refine ⟨313310055658407305519857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417746740877876407359809 313310055658407305519857)
            ·
              refine ⟨234982541743805479139893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313310055658407305519857 234982541743805479139893)
              ·
                refine ⟨22029613288481763669365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234982541743805479139893 22029613288481763669365)
                ·
                  rfl

theorem cell19_72398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_72398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72398 prefixEnd_72398 := by exact prefixLift 72398
  have htrace : WordTrace (prefixWord ++ tailWord_72398) baseStart_72398 baseEnd_72398 := by
    simpa [prefixWord, tailWord_72398, baseEnd_72398] using wordTrace_append hprefix tailTrace_72398
  have hstable : (prefixWord ++ tailWord_72398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72398).length < 2 ^ (prefixWord ++ tailWord_72398).sum := by decide
  have hdescent : baseEnd_72398 < baseStart_72398 := by decide
  rcases family_descends (prefixWord ++ tailWord_72398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72434 : List Nat := [3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_72434 : Nat := 118140960795 + 72434 * 2 ^ 59
def prefixEnd_72434 : Nat := 4983230072969 + 3 ^ 40 * 72434 * 2
def baseEnd_72434 : Nat := 22040567542444346869267

theorem tailTrace_72434 : CollatzResearch.WordTrace tailWord_72434 prefixEnd_72434 22040567542444346869267 := by
  unfold tailWord_72434
  simp only [CollatzResearch.WordTrace]
  refine ⟨660471254897865896856089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1761256679727642391616237 660471254897865896856089)
  ·
    refine ⟨495353441173399422642067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 660471254897865896856089 495353441173399422642067)
    ·
      refine ⟨743030161760099133963101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495353441173399422642067 743030161760099133963101)
      ·
        refine ⟨278636310660037175236163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 743030161760099133963101 278636310660037175236163)
        ·
          refine ⟨417954465990055762854245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278636310660037175236163 417954465990055762854245)
          ·
            refine ⟨78366462373135455535171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 417954465990055762854245 78366462373135455535171)
            ·
              refine ⟨117549693559703183302757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78366462373135455535171 117549693559703183302757)
              ·
                refine ⟨22040567542444346869267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117549693559703183302757 22040567542444346869267)
                ·
                  rfl

theorem cell19_72434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_72434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72434 prefixEnd_72434 := by exact prefixLift 72434
  have htrace : WordTrace (prefixWord ++ tailWord_72434) baseStart_72434 baseEnd_72434 := by
    simpa [prefixWord, tailWord_72434, baseEnd_72434] using wordTrace_append hprefix tailTrace_72434
  have hstable : (prefixWord ++ tailWord_72434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72434).length < 2 ^ (prefixWord ++ tailWord_72434).sum := by decide
  have hdescent : baseEnd_72434 < baseStart_72434 := by decide
  rcases family_descends (prefixWord ++ tailWord_72434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72457 : List Nat := [1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_72457 : Nat := 118140960795 + 72457 * 2 ^ 59
def prefixEnd_72457 : Nat := 4983230072969 + 3 ^ 40 * 72457 * 2
def baseEnd_72457 : Nat := 22047566093587108358093

theorem tailTrace_72457 : CollatzResearch.WordTrace tailWord_72457 prefixEnd_72457 22047566093587108358093 := by
  unfold tailWord_72457
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642723898508138515511625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1761815932338759010341083 2642723898508138515511625)
  ·
    refine ⟨1982042923881103886633719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2642723898508138515511625 1982042923881103886633719)
    ·
      refine ⟨2973064385821655829950579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982042923881103886633719 2973064385821655829950579)
      ·
        refine ⟨4459596578732483744925869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973064385821655829950579 4459596578732483744925869)
        ·
          refine ⟨1672348717024681404347201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4459596578732483744925869 1672348717024681404347201)
          ·
            refine ⟨1254261537768511053260401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672348717024681404347201 1254261537768511053260401)
            ·
              refine ⟨940696153326383289945301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254261537768511053260401 940696153326383289945301)
              ·
                refine ⟨22047566093587108358093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 940696153326383289945301 22047566093587108358093)
                ·
                  rfl

theorem cell19_72457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_72457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72457 prefixEnd_72457 := by exact prefixLift 72457
  have htrace : WordTrace (prefixWord ++ tailWord_72457) baseStart_72457 baseEnd_72457 := by
    simpa [prefixWord, tailWord_72457, baseEnd_72457] using wordTrace_append hprefix tailTrace_72457
  have hstable : (prefixWord ++ tailWord_72457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72457).length < 2 ^ (prefixWord ++ tailWord_72457).sum := by decide
  have hdescent : baseEnd_72457 < baseStart_72457 := by decide
  rcases family_descends (prefixWord ++ tailWord_72457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72510 : List Nat := [4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_72510 : Nat := 118140960795 + 72510 * 2 ^ 59
def prefixEnd_72510 : Nat := 4983230072969 + 3 ^ 40 * 72510 * 2
def baseEnd_72510 : Nat := 22063693189698689180171

theorem tailTrace_72510 : CollatzResearch.WordTrace tailWord_72510 prefixEnd_72510 22063693189698689180171 := by
  unfold tailWord_72510
  simp only [CollatzResearch.WordTrace]
  refine ⟨330582120914516070898873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1763104644877419044793989 330582120914516070898873)
  ·
    refine ⟨247936590685887053174155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 330582120914516070898873 247936590685887053174155)
    ·
      refine ⟨371904886028830579761233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247936590685887053174155 371904886028830579761233)
      ·
        refine ⟨278928664521622934820925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371904886028830579761233 278928664521622934820925)
        ·
          refine ⟨104598249195608600557847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278928664521622934820925 104598249195608600557847)
          ·
            refine ⟨156897373793412900836771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104598249195608600557847 156897373793412900836771)
            ·
              refine ⟨235346060690119351255157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156897373793412900836771 235346060690119351255157)
              ·
                refine ⟨22063693189698689180171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235346060690119351255157 22063693189698689180171)
                ·
                  rfl

theorem cell19_72510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_72510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72510 prefixEnd_72510 := by exact prefixLift 72510
  have htrace : WordTrace (prefixWord ++ tailWord_72510) baseStart_72510 baseEnd_72510 := by
    simpa [prefixWord, tailWord_72510, baseEnd_72510] using wordTrace_append hprefix tailTrace_72510
  have hstable : (prefixWord ++ tailWord_72510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72510).length < 2 ^ (prefixWord ++ tailWord_72510).sum := by decide
  have hdescent : baseEnd_72510 < baseStart_72510 := by decide
  rcases family_descends (prefixWord ++ tailWord_72510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72529 : List Nat := [1, 2, 2, 1, 7, 1, 5]
def baseStart_72529 : Nat := 118140960795 + 72529 * 2 ^ 59
def prefixEnd_72529 : Nat := 4983230072969 + 3 ^ 40 * 72529 * 2
def baseEnd_72529 : Nat := 7356491533837424919299

theorem tailTrace_72529 : CollatzResearch.WordTrace tailWord_72529 prefixEnd_72529 7356491533837424919299 := by
  unfold tailWord_72529
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645349954247294812132641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1763566636164863208088427 2645349954247294812132641)
  ·
    refine ⟨1984012465685471109099481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2645349954247294812132641 1984012465685471109099481)
    ·
      refine ⟨1488009349264103331824611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1984012465685471109099481 1488009349264103331824611)
      ·
        refine ⟨2232014023896154997736917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488009349264103331824611 2232014023896154997736917)
        ·
          refine ⟨52312828685066132759459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2232014023896154997736917 52312828685066132759459)
          ·
            refine ⟨78469243027599199139189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52312828685066132759459 78469243027599199139189)
            ·
              refine ⟨7356491533837424919299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78469243027599199139189 7356491533837424919299)
              ·
                rfl

theorem cell19_72529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_72529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72529 prefixEnd_72529 := by exact prefixLift 72529
  have htrace : WordTrace (prefixWord ++ tailWord_72529) baseStart_72529 baseEnd_72529 := by
    simpa [prefixWord, tailWord_72529, baseEnd_72529] using wordTrace_append hprefix tailTrace_72529
  have hstable : (prefixWord ++ tailWord_72529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72529).length < 2 ^ (prefixWord ++ tailWord_72529).sum := by decide
  have hdescent : baseEnd_72529 < baseStart_72529 := by decide
  rcases family_descends (prefixWord ++ tailWord_72529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72571 : List Nat := [1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_72571 : Nat := 118140960795 + 72571 * 2 ^ 59
def prefixEnd_72571 : Nat := 4983230072969 + 3 ^ 40 * 72571 * 2
def baseEnd_72571 : Nat := 22082254564468621824449

theorem tailTrace_72571 : CollatzResearch.WordTrace tailWord_72571 prefixEnd_72571 22082254564468621824449 := by
  unfold tailWord_72571
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646881820095135985161567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1764587880063423990107711 2646881820095135985161567)
  ·
    refine ⟨3970322730142703977742351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646881820095135985161567 3970322730142703977742351)
    ·
      refine ⟨5955484095214055966613527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970322730142703977742351 5955484095214055966613527)
      ·
        refine ⟨8933226142821083949920291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5955484095214055966613527 8933226142821083949920291)
        ·
          refine ⟨13399839214231625924880437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8933226142821083949920291 13399839214231625924880437)
          ·
            refine ⟨1256234926334214930457541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13399839214231625924880437 1256234926334214930457541)
            ·
              refine ⟨235544048687665299460789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1256234926334214930457541 235544048687665299460789)
              ·
                refine ⟨22082254564468621824449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235544048687665299460789 22082254564468621824449)
                ·
                  rfl

theorem cell19_72571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_72571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72571 prefixEnd_72571 := by exact prefixLift 72571
  have htrace : WordTrace (prefixWord ++ tailWord_72571) baseStart_72571 baseEnd_72571 := by
    simpa [prefixWord, tailWord_72571, baseEnd_72571] using wordTrace_append hprefix tailTrace_72571
  have hstable : (prefixWord ++ tailWord_72571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72571).length < 2 ^ (prefixWord ++ tailWord_72571).sum := by decide
  have hdescent : baseEnd_72571 < baseStart_72571 := by decide
  rcases family_descends (prefixWord ++ tailWord_72571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72590 : List Nat := [4, 1, 1, 13]
def baseStart_72590 : Nat := 118140960795 + 72590 * 2 ^ 59
def prefixEnd_72590 : Nat := 4983230072969 + 3 ^ 40 * 72590 * 2
def baseEnd_72590 : Nat := 272691802176323548175

theorem tailTrace_72590 : CollatzResearch.WordTrace tailWord_72590 prefixEnd_72590 272691802176323548175 := by
  unfold tailWord_72590
  simp only [CollatzResearch.WordTrace]
  refine ⟨330946850878287778762903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1765049871350868153402149 330946850878287778762903)
  ·
    refine ⟨496420276317431668144355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 330946850878287778762903 496420276317431668144355)
    ·
      refine ⟨744630414476147502216533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496420276317431668144355 744630414476147502216533)
      ·
        refine ⟨272691802176323548175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 744630414476147502216533 272691802176323548175)
        ·
          rfl

theorem cell19_72590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 13].length) (baseStart_72590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72590 prefixEnd_72590 := by exact prefixLift 72590
  have htrace : WordTrace (prefixWord ++ tailWord_72590) baseStart_72590 baseEnd_72590 := by
    simpa [prefixWord, tailWord_72590, baseEnd_72590] using wordTrace_append hprefix tailTrace_72590
  have hstable : (prefixWord ++ tailWord_72590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72590).length < 2 ^ (prefixWord ++ tailWord_72590).sum := by decide
  have hdescent : baseEnd_72590 < baseStart_72590 := by decide
  rcases family_descends (prefixWord ++ tailWord_72590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72607 : List Nat := [1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_72607 : Nat := 118140960795 + 72607 * 2 ^ 59
def prefixEnd_72607 : Nat := 4983230072969 + 3 ^ 40 * 72607 * 2
def baseEnd_72607 : Nat := 22093208818431205024351

theorem tailTrace_72607 : CollatzResearch.WordTrace tailWord_72607 prefixEnd_72607 22093208818431205024351 := by
  unfold tailWord_72607
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648194847964714133472075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1765463231976476088981383 2648194847964714133472075)
  ·
    refine ⟨3972292271947071200208113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2648194847964714133472075 3972292271947071200208113)
    ·
      refine ⟨2979219203960303400156085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3972292271947071200208113 2979219203960303400156085)
      ·
        refine ⟨279301800371278443764633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2979219203960303400156085 279301800371278443764633)
        ·
          refine ⟨209476350278458832823475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279301800371278443764633 209476350278458832823475)
          ·
            refine ⟨314214525417688249235213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209476350278458832823475 314214525417688249235213)
            ·
              refine ⟨117830447031633093463205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314214525417688249235213 117830447031633093463205)
              ·
                refine ⟨22093208818431205024351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117830447031633093463205 22093208818431205024351)
                ·
                  rfl

theorem cell19_72607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_72607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72607 prefixEnd_72607 := by exact prefixLift 72607
  have htrace : WordTrace (prefixWord ++ tailWord_72607) baseStart_72607 baseEnd_72607 := by
    simpa [prefixWord, tailWord_72607, baseEnd_72607] using wordTrace_append hprefix tailTrace_72607
  have hstable : (prefixWord ++ tailWord_72607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72607).length < 2 ^ (prefixWord ++ tailWord_72607).sum := by decide
  have hdescent : baseEnd_72607 < baseStart_72607 := by decide
  rcases family_descends (prefixWord ++ tailWord_72607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72677 : List Nat := [1, 3, 1, 6, 2, 1, 2, 3]
def baseStart_72677 : Nat := 118140960795 + 72677 * 2 ^ 59
def prefixEnd_72677 : Nat := 4983230072969 + 3 ^ 40 * 72677 * 2
def baseEnd_72677 : Nat := 22114508756691783468605

theorem tailTrace_72677 : CollatzResearch.WordTrace tailWord_72677 prefixEnd_72677 22114508756691783468605 := by
  unfold tailWord_72677
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650747957711116088520285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1767165305140744059013523 2650747957711116088520285)
  ·
    refine ⟨994030484141668533195107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2650747957711116088520285 994030484141668533195107)
    ·
      refine ⟨1491045726212502799792661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994030484141668533195107 1491045726212502799792661)
      ·
        refine ⟨69892768416211068740281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1491045726212502799792661 69892768416211068740281)
        ·
          refine ⟨52419576312158301555211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69892768416211068740281 52419576312158301555211)
          ·
            refine ⟨78629364468237452332817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52419576312158301555211 78629364468237452332817)
            ·
              refine ⟨58972023351178089249613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78629364468237452332817 58972023351178089249613)
              ·
                refine ⟨22114508756691783468605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58972023351178089249613 22114508756691783468605)
                ·
                  rfl

theorem cell19_72677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_72677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72677 prefixEnd_72677 := by exact prefixLift 72677
  have htrace : WordTrace (prefixWord ++ tailWord_72677) baseStart_72677 baseEnd_72677 := by
    simpa [prefixWord, tailWord_72677, baseEnd_72677] using wordTrace_append hprefix tailTrace_72677
  have hstable : (prefixWord ++ tailWord_72677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72677).length < 2 ^ (prefixWord ++ tailWord_72677).sum := by decide
  have hdescent : baseEnd_72677 < baseStart_72677 := by decide
  rcases family_descends (prefixWord ++ tailWord_72677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72740 : List Nat := [2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_72740 : Nat := 118140960795 + 72740 * 2 ^ 59
def prefixEnd_72740 : Nat := 4983230072969 + 3 ^ 40 * 72740 * 2
def baseEnd_72740 : Nat := 22133678701126304068433

theorem tailTrace_72740 : CollatzResearch.WordTrace tailWord_72740 prefixEnd_72740 22133678701126304068433 := by
  unfold tailWord_72740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326522878241438924031837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1768697170988585232042449 1326522878241438924031837)
  ·
    refine ⟨497446079340539596511939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1326522878241438924031837 497446079340539596511939)
    ·
      refine ⟨746169119010809394767909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497446079340539596511939 746169119010809394767909)
      ·
        refine ⟨139906709814526761518983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 746169119010809394767909 139906709814526761518983)
        ·
          refine ⟨209860064721790142278475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139906709814526761518983 209860064721790142278475)
          ·
            refine ⟨314790097082685213417713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209860064721790142278475 314790097082685213417713)
            ·
              refine ⟨236092572812013910063285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314790097082685213417713 236092572812013910063285)
              ·
                refine ⟨22133678701126304068433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 236092572812013910063285 22133678701126304068433)
                ·
                  rfl

theorem cell19_72740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_72740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72740 prefixEnd_72740 := by exact prefixLift 72740
  have htrace : WordTrace (prefixWord ++ tailWord_72740) baseStart_72740 baseEnd_72740 := by
    simpa [prefixWord, tailWord_72740, baseEnd_72740] using wordTrace_append hprefix tailTrace_72740
  have hstable : (prefixWord ++ tailWord_72740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72740).length < 2 ^ (prefixWord ++ tailWord_72740).sum := by decide
  have hdescent : baseEnd_72740 < baseStart_72740 := by decide
  rcases family_descends (prefixWord ++ tailWord_72740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72761 : List Nat := [1, 2, 1, 5, 2, 8]
def baseStart_72761 : Nat := 118140960795 + 72761 * 2 ^ 59
def prefixEnd_72761 : Nat := 4983230072969 + 3 ^ 40 * 72761 * 2
def baseEnd_72761 : Nat := 2460007631400497511301

theorem tailTrace_72761 : CollatzResearch.WordTrace tailWord_72761 prefixEnd_72761 2460007631400497511301 := by
  unfold tailWord_72761
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653811689406798434578137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1769207792937865623052091 2653811689406798434578137)
  ·
    refine ⟨1990358767055098825933603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2653811689406798434578137 1990358767055098825933603)
    ·
      refine ⟨2985538150582648238900405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990358767055098825933603 2985538150582648238900405)
      ·
        refine ⟨279894201617123272396913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2985538150582648238900405 279894201617123272396913)
        ·
          refine ⟨209920651212842454297685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279894201617123272396913 209920651212842454297685)
          ·
            refine ⟨2460007631400497511301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 209920651212842454297685 2460007631400497511301)
            ·
              rfl

theorem cell19_72761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_72761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72761 prefixEnd_72761 := by exact prefixLift 72761
  have htrace : WordTrace (prefixWord ++ tailWord_72761) baseStart_72761 baseEnd_72761 := by
    simpa [prefixWord, tailWord_72761, baseEnd_72761] using wordTrace_append hprefix tailTrace_72761
  have hstable : (prefixWord ++ tailWord_72761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72761).length < 2 ^ (prefixWord ++ tailWord_72761).sum := by decide
  have hdescent : baseEnd_72761 < baseStart_72761 := by decide
  rcases family_descends (prefixWord ++ tailWord_72761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72774 : List Nat := [6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_72774 : Nat := 118140960795 + 72774 * 2 ^ 59
def prefixEnd_72774 : Nat := 4983230072969 + 3 ^ 40 * 72774 * 2
def baseEnd_72774 : Nat := 22144024385424299312785

theorem tailTrace_72774 : CollatzResearch.WordTrace tailWord_72774 prefixEnd_72774 22144024385424299312785 := by
  unfold tailWord_72774
  simp only [CollatzResearch.WordTrace]
  refine ⟨82946432448740676712543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1769523892239801103200917 82946432448740676712543)
  ·
    refine ⟨124419648673111015068815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82946432448740676712543 124419648673111015068815)
    ·
      refine ⟨186629473009666522603223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124419648673111015068815 186629473009666522603223)
      ·
        refine ⟨279944209514499783904835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186629473009666522603223 279944209514499783904835)
        ·
          refine ⟨419916314271749675857253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279944209514499783904835 419916314271749675857253)
          ·
            refine ⟨78734308925953064223235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 419916314271749675857253 78734308925953064223235)
            ·
              refine ⟨118101463388929596334853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78734308925953064223235 118101463388929596334853)
              ·
                refine ⟨22144024385424299312785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118101463388929596334853 22144024385424299312785)
                ·
                  rfl

theorem cell19_72774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_72774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72774 prefixEnd_72774 := by exact prefixLift 72774
  have htrace : WordTrace (prefixWord ++ tailWord_72774) baseStart_72774 baseEnd_72774 := by
    simpa [prefixWord, tailWord_72774, baseEnd_72774] using wordTrace_append hprefix tailTrace_72774
  have hstable : (prefixWord ++ tailWord_72774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72774).length < 2 ^ (prefixWord ++ tailWord_72774).sum := by decide
  have hdescent : baseEnd_72774 < baseStart_72774 := by decide
  rcases family_descends (prefixWord ++ tailWord_72774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72818 : List Nat := [3, 2, 1, 2, 2, 1, 8]
def baseStart_72818 : Nat := 118140960795 + 72818 * 2 ^ 59
def prefixEnd_72818 : Nat := 4983230072969 + 3 ^ 40 * 72818 * 2
def baseEnd_72818 : Nat := 7385804306015078111629

theorem tailTrace_72818 : CollatzResearch.WordTrace tailWord_72818 prefixEnd_72818 7385804306015078111629 := by
  unfold tailWord_72818
  simp only [CollatzResearch.WordTrace]
  refine ⟨663972662550074292350777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1770593766800198112935405 663972662550074292350777)
  ·
    refine ⟨497979496912555719263083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 663972662550074292350777 497979496912555719263083)
    ·
      refine ⟨746969245368833578894625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497979496912555719263083 746969245368833578894625)
      ·
        refine ⟨560226934026625184170969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 746969245368833578894625 560226934026625184170969)
        ·
          refine ⟨420170200519968888128227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560226934026625184170969 420170200519968888128227)
          ·
            refine ⟨630255300779953332192341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420170200519968888128227 630255300779953332192341)
            ·
              refine ⟨7385804306015078111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 630255300779953332192341 7385804306015078111629)
              ·
                rfl

theorem cell19_72818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_72818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72818 prefixEnd_72818 := by exact prefixLift 72818
  have htrace : WordTrace (prefixWord ++ tailWord_72818) baseStart_72818 baseEnd_72818 := by
    simpa [prefixWord, tailWord_72818, baseEnd_72818] using wordTrace_append hprefix tailTrace_72818
  have hstable : (prefixWord ++ tailWord_72818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72818).length < 2 ^ (prefixWord ++ tailWord_72818).sum := by decide
  have hdescent : baseEnd_72818 < baseStart_72818 := by decide
  rcases family_descends (prefixWord ++ tailWord_72818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72892 : List Nat := [2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_72892 : Nat := 118140960795 + 72892 * 2 ^ 59
def prefixEnd_72892 : Nat := 4983230072969 + 3 ^ 40 * 72892 * 2
def baseEnd_72892 : Nat := 22179929995634988690241

theorem tailTrace_72892 : CollatzResearch.WordTrace tailWord_72892 prefixEnd_72892 22179929995634988690241 := by
  unfold tailWord_72892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329294825966103903798465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1772393101288138538397953 1329294825966103903798465)
  ·
    refine ⟨996971119474577927848849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1329294825966103903798465 996971119474577927848849)
    ·
      refine ⟨747728339605933445886637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 996971119474577927848849 747728339605933445886637)
      ·
        refine ⟨280398127352225042207489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 747728339605933445886637 280398127352225042207489)
        ·
          refine ⟨210298595514168781655617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280398127352225042207489 210298595514168781655617)
          ·
            refine ⟨157723946635626586241713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210298595514168781655617 157723946635626586241713)
            ·
              refine ⟨118292959976719939681285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157723946635626586241713 118292959976719939681285)
              ·
                refine ⟨22179929995634988690241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118292959976719939681285 22179929995634988690241)
                ·
                  rfl

theorem cell19_72892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_72892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72892 prefixEnd_72892 := by exact prefixLift 72892
  have htrace : WordTrace (prefixWord ++ tailWord_72892) baseStart_72892 baseEnd_72892 := by
    simpa [prefixWord, tailWord_72892, baseEnd_72892] using wordTrace_append hprefix tailTrace_72892
  have hstable : (prefixWord ++ tailWord_72892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72892).length < 2 ^ (prefixWord ++ tailWord_72892).sum := by decide
  have hdescent : baseEnd_72892 < baseStart_72892 := by decide
  rcases family_descends (prefixWord ++ tailWord_72892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72930 : List Nat := [3, 3, 4, 9]
def baseStart_72930 : Nat := 118140960795 + 72930 * 2 ^ 59
def prefixEnd_72930 : Nat := 4983230072969 + 3 ^ 40 * 72930 * 2
def baseEnd_72930 : Nat := 273969047151384689453

theorem tailTrace_72930 : CollatzResearch.WordTrace tailWord_72930 prefixEnd_72930 273969047151384689453 := by
  unfold tailWord_72930
  simp only [CollatzResearch.WordTrace]
  refine ⟨664993906448635074370061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1773317083863026864986829 664993906448635074370061)
  ·
    refine ⟨249372714918238152888773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 664993906448635074370061 249372714918238152888773)
    ·
      refine ⟨46757384047169653666645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249372714918238152888773 46757384047169653666645)
      ·
        refine ⟨273969047151384689453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 46757384047169653666645 273969047151384689453)
        ·
          rfl

theorem cell19_72930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 9].length) (baseStart_72930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_72930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_72930 prefixEnd_72930 := by exact prefixLift 72930
  have htrace : WordTrace (prefixWord ++ tailWord_72930) baseStart_72930 baseEnd_72930 := by
    simpa [prefixWord, tailWord_72930, baseEnd_72930] using wordTrace_append hprefix tailTrace_72930
  have hstable : (prefixWord ++ tailWord_72930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72930).length < 2 ^ (prefixWord ++ tailWord_72930).sum := by decide
  have hdescent : baseEnd_72930 < baseStart_72930 := by decide
  rcases family_descends (prefixWord ++ tailWord_72930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73021 : List Nat := [1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_73021 : Nat := 118140960795 + 73021 * 2 ^ 59
def prefixEnd_73021 : Nat := 4983230072969 + 3 ^ 40 * 73021 * 2
def baseEnd_73021 : Nat := 22219182739000911823223

theorem tailTrace_73021 : CollatzResearch.WordTrace tailWord_73021 prefixEnd_73021 22219182739000911823223 := by
  unfold tailWord_73021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663294668464862839042917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1775529778976575226028611 2663294668464862839042917)
  ·
    refine ⟨499367750337161782320547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2663294668464862839042917 499367750337161782320547)
    ·
      refine ⟨749051625505742673480821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499367750337161782320547 749051625505742673480821)
      ·
        refine ⟨70223589891163375638827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 749051625505742673480821 70223589891163375638827)
        ·
          refine ⟨105335384836745063458241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70223589891163375638827 105335384836745063458241)
          ·
            refine ⟨79001538627558797593681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105335384836745063458241 79001538627558797593681)
            ·
              refine ⟨59251153970669098195261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79001538627558797593681 59251153970669098195261)
              ·
                refine ⟨22219182739000911823223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59251153970669098195261 22219182739000911823223)
                ·
                  rfl

theorem cell19_73021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_73021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73021 prefixEnd_73021 := by exact prefixLift 73021
  have htrace : WordTrace (prefixWord ++ tailWord_73021) baseStart_73021 baseEnd_73021 := by
    simpa [prefixWord, tailWord_73021, baseEnd_73021] using wordTrace_append hprefix tailTrace_73021
  have hstable : (prefixWord ++ tailWord_73021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73021).length < 2 ^ (prefixWord ++ tailWord_73021).sum := by decide
  have hdescent : baseEnd_73021 < baseStart_73021 := by decide
  rcases family_descends (prefixWord ++ tailWord_73021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73025 : List Nat := [1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_73025 : Nat := 118140960795 + 73025 * 2 ^ 59
def prefixEnd_73025 : Nat := 4983230072969 + 3 ^ 40 * 73025 * 2
def baseEnd_73025 : Nat := 22220399878330087734323

theorem tailTrace_73025 : CollatzResearch.WordTrace tailWord_73025 prefixEnd_73025 22220399878330087734323 := by
  unfold tailWord_73025
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663440560450371522188529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1775627040300247681459019 2663440560450371522188529)
  ·
    refine ⟨1997580420337778641641397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2663440560450371522188529 1997580420337778641641397)
    ·
      refine ⟨187273164406666747653881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1997580420337778641641397 187273164406666747653881)
      ·
        refine ⟨140454873305000060740411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187273164406666747653881 140454873305000060740411)
        ·
          refine ⟨210682309957500091110617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140454873305000060740411 210682309957500091110617)
          ·
            refine ⟨158011732468125068332963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210682309957500091110617 158011732468125068332963)
            ·
              refine ⟨237017598702187602499445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158011732468125068332963 237017598702187602499445)
              ·
                refine ⟨22220399878330087734323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237017598702187602499445 22220399878330087734323)
                ·
                  rfl

theorem cell19_73025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_73025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73025 prefixEnd_73025 := by exact prefixLift 73025
  have htrace : WordTrace (prefixWord ++ tailWord_73025) baseStart_73025 baseEnd_73025 := by
    simpa [prefixWord, tailWord_73025, baseEnd_73025] using wordTrace_append hprefix tailTrace_73025
  have hstable : (prefixWord ++ tailWord_73025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73025).length < 2 ^ (prefixWord ++ tailWord_73025).sum := by decide
  have hdescent : baseEnd_73025 < baseStart_73025 := by decide
  rcases family_descends (prefixWord ++ tailWord_73025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73063 : List Nat := [1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_73063 : Nat := 118140960795 + 73063 * 2 ^ 59
def prefixEnd_73063 : Nat := 4983230072969 + 3 ^ 40 * 73063 * 2
def baseEnd_73063 : Nat := 22231962701957258889775

theorem tailTrace_73063 : CollatzResearch.WordTrace tailWord_73063 prefixEnd_73063 22231962701957258889775 := by
  unfold tailWord_73063
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664826534312704012071843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1776551022875136008047895 2664826534312704012071843)
  ·
    refine ⟨3997239801469056018107765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2664826534312704012071843 3997239801469056018107765)
    ·
      refine ⟨374741231387724001697603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3997239801469056018107765 374741231387724001697603)
      ·
        refine ⟨562111847081586002546405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374741231387724001697603 562111847081586002546405)
        ·
          refine ⟨105395971327797375477451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 562111847081586002546405 105395971327797375477451)
          ·
            refine ⟨158093956991696063216177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105395971327797375477451 158093956991696063216177)
            ·
              refine ⟨118570467743772047412133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158093956991696063216177 118570467743772047412133)
              ·
                refine ⟨22231962701957258889775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118570467743772047412133 22231962701957258889775)
                ·
                  rfl

theorem cell19_73063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_73063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73063 prefixEnd_73063 := by exact prefixLift 73063
  have htrace : WordTrace (prefixWord ++ tailWord_73063) baseStart_73063 baseEnd_73063 := by
    simpa [prefixWord, tailWord_73063, baseEnd_73063] using wordTrace_append hprefix tailTrace_73063
  have hstable : (prefixWord ++ tailWord_73063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73063).length < 2 ^ (prefixWord ++ tailWord_73063).sum := by decide
  have hdescent : baseEnd_73063 < baseStart_73063 := by decide
  rcases family_descends (prefixWord ++ tailWord_73063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73116 : List Nat := [2, 2, 3, 4, 2, 1, 1, 4]
def baseStart_73116 : Nat := 118140960795 + 73116 * 2 ^ 59
def prefixEnd_73116 : Nat := 4983230072969 + 3 ^ 40 * 73116 * 2
def baseEnd_73116 : Nat := 22248089798068839711853

theorem tailTrace_73116 : CollatzResearch.WordTrace tailWord_73116 prefixEnd_73116 22248089798068839711853 := by
  unfold tailWord_73116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333379801560347031875601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1777839735413796042500801 1333379801560347031875601)
  ·
    refine ⟨1000034851170260273906701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1333379801560347031875601 1000034851170260273906701)
    ·
      refine ⟨375013069188847602715013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1000034851170260273906701 375013069188847602715013)
      ·
        refine ⟨70314950472908925509065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 375013069188847602715013 70314950472908925509065)
        ·
          refine ⟨52736212854681694131799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70314950472908925509065 52736212854681694131799)
          ·
            refine ⟨79104319282022541197699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52736212854681694131799 79104319282022541197699)
            ·
              refine ⟨118656478923033811796549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79104319282022541197699 118656478923033811796549)
              ·
                refine ⟨22248089798068839711853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118656478923033811796549 22248089798068839711853)
                ·
                  rfl

theorem cell19_73116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_73116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73116 prefixEnd_73116 := by exact prefixLift 73116
  have htrace : WordTrace (prefixWord ++ tailWord_73116) baseStart_73116 baseEnd_73116 := by
    simpa [prefixWord, tailWord_73116, baseEnd_73116] using wordTrace_append hprefix tailTrace_73116
  have hstable : (prefixWord ++ tailWord_73116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73116).length < 2 ^ (prefixWord ++ tailWord_73116).sum := by decide
  have hdescent : baseEnd_73116 < baseStart_73116 := by decide
  rcases family_descends (prefixWord ++ tailWord_73116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73194 : List Nat := [3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_73194 : Nat := 118140960795 + 73194 * 2 ^ 59
def prefixEnd_73194 : Nat := 4983230072969 + 3 ^ 40 * 73194 * 2
def baseEnd_73194 : Nat := 22271824014987769978307

theorem tailTrace_73194 : CollatzResearch.WordTrace tailWord_73194 prefixEnd_73194 22271824014987769978307 := by
  unfold tailWord_73194
  simp only [CollatzResearch.WordTrace]
  refine ⟨667401124209528346272659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1779736331225408923393757 667401124209528346272659)
  ·
    refine ⟨1001101686314292519408989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 667401124209528346272659 1001101686314292519408989)
    ·
      refine ⟨375413132367859694778371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1001101686314292519408989 375413132367859694778371)
      ·
        refine ⟨563119698551789542167557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375413132367859694778371 563119698551789542167557)
        ·
          refine ⟨105584943478460539156417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 563119698551789542167557 105584943478460539156417)
          ·
            refine ⟨79188707608845404367313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105584943478460539156417 79188707608845404367313)
            ·
              refine ⟨59391530706634053275485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79188707608845404367313 59391530706634053275485)
              ·
                refine ⟨22271824014987769978307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59391530706634053275485 22271824014987769978307)
                ·
                  rfl

theorem cell19_73194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_73194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73194 prefixEnd_73194 := by exact prefixLift 73194
  have htrace : WordTrace (prefixWord ++ tailWord_73194) baseStart_73194 baseEnd_73194 := by
    simpa [prefixWord, tailWord_73194, baseEnd_73194] using wordTrace_append hprefix tailTrace_73194
  have hstable : (prefixWord ++ tailWord_73194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73194).length < 2 ^ (prefixWord ++ tailWord_73194).sum := by decide
  have hdescent : baseEnd_73194 < baseStart_73194 := by decide
  rcases family_descends (prefixWord ++ tailWord_73194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73198 : List Nat := [4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_73198 : Nat := 118140960795 + 73198 * 2 ^ 59
def prefixEnd_73198 : Nat := 4983230072969 + 3 ^ 40 * 73198 * 2
def baseEnd_73198 : Nat := 22273041154316945889407

theorem tailTrace_73198 : CollatzResearch.WordTrace tailWord_73198 prefixEnd_73198 22273041154316945889407 := by
  unfold tailWord_73198
  simp only [CollatzResearch.WordTrace]
  refine ⟨333718798602952758529531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1779833592549081378824165 333718798602952758529531)
  ·
    refine ⟨500578197904429137794297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 333718798602952758529531 500578197904429137794297)
    ·
      refine ⟨375433648428321853345723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 500578197904429137794297 375433648428321853345723)
      ·
        refine ⟨563150472642482780018585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375433648428321853345723 563150472642482780018585)
        ·
          refine ⟨422362854481862085013939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563150472642482780018585 422362854481862085013939)
          ·
            refine ⟨633544281722793127520909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422362854481862085013939 633544281722793127520909)
            ·
              refine ⟨237579105646047422820341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 633544281722793127520909 237579105646047422820341)
              ·
                refine ⟨22273041154316945889407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237579105646047422820341 22273041154316945889407)
                ·
                  rfl

theorem cell19_73198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_73198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73198 prefixEnd_73198 := by exact prefixLift 73198
  have htrace : WordTrace (prefixWord ++ tailWord_73198) baseStart_73198 baseEnd_73198 := by
    simpa [prefixWord, tailWord_73198, baseEnd_73198] using wordTrace_append hprefix tailTrace_73198
  have hstable : (prefixWord ++ tailWord_73198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73198).length < 2 ^ (prefixWord ++ tailWord_73198).sum := by decide
  have hdescent : baseEnd_73198 < baseStart_73198 := by decide
  rcases family_descends (prefixWord ++ tailWord_73198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73276 : List Nat := [2, 2, 2, 2, 11]
def baseStart_73276 : Nat := 118140960795 + 73276 * 2 ^ 59
def prefixEnd_73276 : Nat := 4983230072969 + 3 ^ 40 * 73276 * 2
def baseEnd_73276 : Nat := 825806495230958376143

theorem tailTrace_73276 : CollatzResearch.WordTrace tailWord_73276 prefixEnd_73276 825806495230958376143 := by
  unfold tailWord_73276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336297641270520694787841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1781730188360694259717121 1336297641270520694787841)
  ·
    refine ⟨1002223230952890521090881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1336297641270520694787841 1002223230952890521090881)
    ·
      refine ⟨751667423214667890818161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002223230952890521090881 751667423214667890818161)
      ·
        refine ⟨563750567411000918113621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751667423214667890818161 563750567411000918113621)
        ·
          refine ⟨825806495230958376143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 563750567411000918113621 825806495230958376143)
          ·
            rfl

theorem cell19_73276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 11].length) (baseStart_73276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73276 prefixEnd_73276 := by exact prefixLift 73276
  have htrace : WordTrace (prefixWord ++ tailWord_73276) baseStart_73276 baseEnd_73276 := by
    simpa [prefixWord, tailWord_73276, baseEnd_73276] using wordTrace_append hprefix tailTrace_73276
  have hstable : (prefixWord ++ tailWord_73276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73276).length < 2 ^ (prefixWord ++ tailWord_73276).sum := by decide
  have hdescent : baseEnd_73276 < baseStart_73276 := by decide
  rcases family_descends (prefixWord ++ tailWord_73276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73367 : List Nat := [1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_73367 : Nat := 118140960795 + 73367 * 2 ^ 59
def prefixEnd_73367 : Nat := 4983230072969 + 3 ^ 40 * 73367 * 2
def baseEnd_73367 : Nat := 22324465290974628133391

theorem tailTrace_73367 : CollatzResearch.WordTrace tailWord_73367 prefixEnd_73367 22324465290974628133391 := by
  unfold tailWord_73367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675914325211363931138355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1783942883474242620758903 2675914325211363931138355)
  ·
    refine ⟨4013871487817045896707533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675914325211363931138355 4013871487817045896707533)
    ·
      refine ⟨1505201807931392211265325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4013871487817045896707533 1505201807931392211265325)
      ·
        refine ⟨564450677974272079224497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1505201807931392211265325 564450677974272079224497)
        ·
          refine ⟨423338008480704059418373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564450677974272079224497 423338008480704059418373)
          ·
            refine ⟨79375876590132011140945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 423338008480704059418373 79375876590132011140945)
            ·
              refine ⟨59531907442599008355709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79375876590132011140945 59531907442599008355709)
              ·
                refine ⟨22324465290974628133391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59531907442599008355709 22324465290974628133391)
                ·
                  rfl

theorem cell19_73367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_73367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73367 prefixEnd_73367 := by exact prefixLift 73367
  have htrace : WordTrace (prefixWord ++ tailWord_73367) baseStart_73367 baseEnd_73367 := by
    simpa [prefixWord, tailWord_73367, baseEnd_73367] using wordTrace_append hprefix tailTrace_73367
  have hstable : (prefixWord ++ tailWord_73367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73367).length < 2 ^ (prefixWord ++ tailWord_73367).sum := by decide
  have hdescent : baseEnd_73367 < baseStart_73367 := by decide
  rcases family_descends (prefixWord ++ tailWord_73367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73426 : List Nat := [3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_73426 : Nat := 118140960795 + 73426 * 2 ^ 59
def prefixEnd_73426 : Nat := 4983230072969 + 3 ^ 40 * 73426 * 2
def baseEnd_73426 : Nat := 22342418096079972822119

theorem tailTrace_73426 : CollatzResearch.WordTrace tailWord_73426 prefixEnd_73426 22342418096079972822119 := by
  unfold tailWord_73426
  simp only [CollatzResearch.WordTrace]
  refine ⟨669516557999404251884033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1785377487998411338357421 669516557999404251884033)
  ·
    refine ⟨502137418499553188913025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 669516557999404251884033 502137418499553188913025)
    ·
      refine ⟨376603063874664891684769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 502137418499553188913025 376603063874664891684769)
      ·
        refine ⟨282452297905998668763577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376603063874664891684769 282452297905998668763577)
        ·
          refine ⟨211839223429499001572683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282452297905998668763577 211839223429499001572683)
          ·
            refine ⟨317758835144248502359025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211839223429499001572683 317758835144248502359025)
            ·
              refine ⟨238319126358186376769269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317758835144248502359025 238319126358186376769269)
              ·
                refine ⟨22342418096079972822119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 238319126358186376769269 22342418096079972822119)
                ·
                  rfl

theorem cell19_73426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_73426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73426 prefixEnd_73426 := by exact prefixLift 73426
  have htrace : WordTrace (prefixWord ++ tailWord_73426) baseStart_73426 baseEnd_73426 := by
    simpa [prefixWord, tailWord_73426, baseEnd_73426] using wordTrace_append hprefix tailTrace_73426
  have hstable : (prefixWord ++ tailWord_73426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73426).length < 2 ^ (prefixWord ++ tailWord_73426).sum := by decide
  have hdescent : baseEnd_73426 < baseStart_73426 := by decide
  rcases family_descends (prefixWord ++ tailWord_73426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73460 : List Nat := [2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_73460 : Nat := 118140960795 + 73460 * 2 ^ 59
def prefixEnd_73460 : Nat := 4983230072969 + 3 ^ 40 * 73460 * 2
def baseEnd_73460 : Nat := 22352763780377968066471

theorem tailTrace_73460 : CollatzResearch.WordTrace tailWord_73460 prefixEnd_73460 22352763780377968066471 := by
  unfold tailWord_73460
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339653156937220407136917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1786204209249627209515889 1339653156937220407136917)
  ·
    refine ⟨62796241731432206584543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1339653156937220407136917 62796241731432206584543)
    ·
      refine ⟨94194362597148309876815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62796241731432206584543 94194362597148309876815)
      ·
        refine ⟨141291543895722464815223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94194362597148309876815 141291543895722464815223)
        ·
          refine ⟨211937315843583697222835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141291543895722464815223 211937315843583697222835)
          ·
            refine ⟨317905973765375545834253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211937315843583697222835 317905973765375545834253)
            ·
              refine ⟨119214740162015829687845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317905973765375545834253 119214740162015829687845)
              ·
                refine ⟨22352763780377968066471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119214740162015829687845 22352763780377968066471)
                ·
                  rfl

theorem cell19_73460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_73460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73460 prefixEnd_73460 := by exact prefixLift 73460
  have htrace : WordTrace (prefixWord ++ tailWord_73460) baseStart_73460 baseEnd_73460 := by
    simpa [prefixWord, tailWord_73460, baseEnd_73460] using wordTrace_append hprefix tailTrace_73460
  have hstable : (prefixWord ++ tailWord_73460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73460).length < 2 ^ (prefixWord ++ tailWord_73460).sum := by decide
  have hdescent : baseEnd_73460 < baseStart_73460 := by decide
  rcases family_descends (prefixWord ++ tailWord_73460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73462 : List Nat := [5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_73462 : Nat := 118140960795 + 73462 * 2 ^ 59
def prefixEnd_73462 : Nat := 4983230072969 + 3 ^ 40 * 73462 * 2
def baseEnd_73462 : Nat := 22353372350042556022021

theorem tailTrace_73462 : CollatzResearch.WordTrace tailWord_73462 prefixEnd_73462 22353372350042556022021 := by
  unfold tailWord_73462
  simp only [CollatzResearch.WordTrace]
  refine ⟨167461203741699697240415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1786252839911463437231093 167461203741699697240415)
  ·
    refine ⟨251191805612549545860623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167461203741699697240415 251191805612549545860623)
    ·
      refine ⟨376787708418824318790935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251191805612549545860623 376787708418824318790935)
      ·
        refine ⟨565181562628236478186403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376787708418824318790935 565181562628236478186403)
        ·
          refine ⟨847772343942354717279605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565181562628236478186403 847772343942354717279605)
          ·
            refine ⟨79478657244595754744963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 847772343942354717279605 79478657244595754744963)
            ·
              refine ⟨119217985866893632117445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79478657244595754744963 119217985866893632117445)
              ·
                refine ⟨22353372350042556022021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119217985866893632117445 22353372350042556022021)
                ·
                  rfl

theorem cell19_73462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_73462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73462 prefixEnd_73462 := by exact prefixLift 73462
  have htrace : WordTrace (prefixWord ++ tailWord_73462) baseStart_73462 baseEnd_73462 := by
    simpa [prefixWord, tailWord_73462, baseEnd_73462] using wordTrace_append hprefix tailTrace_73462
  have hstable : (prefixWord ++ tailWord_73462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73462).length < 2 ^ (prefixWord ++ tailWord_73462).sum := by decide
  have hdescent : baseEnd_73462 < baseStart_73462 := by decide
  rcases family_descends (prefixWord ++ tailWord_73462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73504 : List Nat := [2, 1, 1, 5, 1, 1, 8]
def baseStart_73504 : Nat := 118140960795 + 73504 * 2 ^ 59
def prefixEnd_73504 : Nat := 4983230072969 + 3 ^ 40 * 73504 * 2
def baseEnd_73504 : Nat := 7455384104332967696191

theorem tailTrace_73504 : CollatzResearch.WordTrace tailWord_73504 prefixEnd_73504 7455384104332967696191 := by
  unfold tailWord_73504
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340455562857518164437783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1787274083810024219250377 1340455562857518164437783)
  ·
    refine ⟨2010683344286277246656675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1340455562857518164437783 2010683344286277246656675)
    ·
      refine ⟨3016025016429415869985013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010683344286277246656675 3016025016429415869985013)
      ·
        refine ⟨282752345290257737811095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3016025016429415869985013 282752345290257737811095)
        ·
          refine ⟨424128517935386606716643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282752345290257737811095 424128517935386606716643)
          ·
            refine ⟨636192776903079910074965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424128517935386606716643 636192776903079910074965)
            ·
              refine ⟨7455384104332967696191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 636192776903079910074965 7455384104332967696191)
              ·
                rfl

theorem cell19_73504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_73504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73504 prefixEnd_73504 := by exact prefixLift 73504
  have htrace : WordTrace (prefixWord ++ tailWord_73504) baseStart_73504 baseEnd_73504 := by
    simpa [prefixWord, tailWord_73504, baseEnd_73504] using wordTrace_append hprefix tailTrace_73504
  have hstable : (prefixWord ++ tailWord_73504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73504).length < 2 ^ (prefixWord ++ tailWord_73504).sum := by decide
  have hdescent : baseEnd_73504 < baseStart_73504 := by decide
  rcases family_descends (prefixWord ++ tailWord_73504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73559 : List Nat := [1, 1, 3, 2, 5, 2, 5]
def baseStart_73559 : Nat := 118140960795 + 73559 * 2 ^ 59
def prefixEnd_73559 : Nat := 4983230072969 + 3 ^ 40 * 73559 * 2
def baseEnd_73559 : Nat := 7460962659591690622067

theorem tailTrace_73559 : CollatzResearch.WordTrace tailWord_73559 prefixEnd_73559 7460962659591690622067 := by
  unfold tailWord_73559
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682917140515780722127731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1788611427010520481418487 2682917140515780722127731)
  ·
    refine ⟨4024375710773671083191597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2682917140515780722127731 4024375710773671083191597)
    ·
      refine ⟨1509140891540126656196849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4024375710773671083191597 1509140891540126656196849)
      ·
        refine ⟨1131855668655094992147637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1509140891540126656196849 1131855668655094992147637)
        ·
          refine ⟨106111468936415155513841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1131855668655094992147637 106111468936415155513841)
          ·
            refine ⟨79583601702311366635381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106111468936415155513841 79583601702311366635381)
            ·
              refine ⟨7460962659591690622067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79583601702311366635381 7460962659591690622067)
              ·
                rfl

theorem cell19_73559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_73559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73559 prefixEnd_73559 := by exact prefixLift 73559
  have htrace : WordTrace (prefixWord ++ tailWord_73559) baseStart_73559 baseEnd_73559 := by
    simpa [prefixWord, tailWord_73559, baseEnd_73559] using wordTrace_append hprefix tailTrace_73559
  have hstable : (prefixWord ++ tailWord_73559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73559).length < 2 ^ (prefixWord ++ tailWord_73559).sum := by decide
  have hdescent : baseEnd_73559 < baseStart_73559 := by decide
  rcases family_descends (prefixWord ++ tailWord_73559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73580 : List Nat := [2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_73580 : Nat := 118140960795 + 73580 * 2 ^ 59
def prefixEnd_73580 : Nat := 4983230072969 + 3 ^ 40 * 73580 * 2
def baseEnd_73580 : Nat := 22389277960253245399477

theorem tailTrace_73580 : CollatzResearch.WordTrace tailWord_73580 prefixEnd_73580 22389277960253245399477 := by
  unfold tailWord_73580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341841536719850654321097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1789122048959800872428129 1341841536719850654321097)
  ·
    refine ⟨1006381152539887990740823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1341841536719850654321097 1006381152539887990740823)
    ·
      refine ⟨1509571728809831986111235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006381152539887990740823 1509571728809831986111235)
      ·
        refine ⟨2264357593214747979166853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509571728809831986111235 2264357593214747979166853)
        ·
          refine ⟨424567048727765246093785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2264357593214747979166853 424567048727765246093785)
          ·
            refine ⟨318425286545823934570339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424567048727765246093785 318425286545823934570339)
            ·
              refine ⟨477637929818735901855509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318425286545823934570339 477637929818735901855509)
              ·
                refine ⟨22389277960253245399477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 477637929818735901855509 22389277960253245399477)
                ·
                  rfl

theorem cell19_73580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_73580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73580 prefixEnd_73580 := by exact prefixLift 73580
  have htrace : WordTrace (prefixWord ++ tailWord_73580) baseStart_73580 baseEnd_73580 := by
    simpa [prefixWord, tailWord_73580, baseEnd_73580] using wordTrace_append hprefix tailTrace_73580
  have hstable : (prefixWord ++ tailWord_73580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73580).length < 2 ^ (prefixWord ++ tailWord_73580).sum := by decide
  have hdescent : baseEnd_73580 < baseStart_73580 := by decide
  rcases family_descends (prefixWord ++ tailWord_73580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73614 : List Nat := [4, 1, 1, 5, 2, 6]
def baseStart_73614 : Nat := 118140960795 + 73614 * 2 ^ 59
def prefixEnd_73614 : Nat := 4983230072969 + 3 ^ 40 * 73614 * 2
def baseEnd_73614 : Nat := 2488847071616804515981

theorem tailTrace_73614 : CollatzResearch.WordTrace tailWord_73614 prefixEnd_73614 2488847071616804515981 := by
  unfold tailWord_73614
  simp only [CollatzResearch.WordTrace]
  refine ⟨335615394414565639422487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1789948770211016743586597 335615394414565639422487)
  ·
    refine ⟨503423091621848459133731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335615394414565639422487 503423091621848459133731)
    ·
      refine ⟨755134637432772688700597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503423091621848459133731 755134637432772688700597)
      ·
        refine ⟨70793872259322439565681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 755134637432772688700597 70793872259322439565681)
        ·
          refine ⟨53095404194491829674261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70793872259322439565681 53095404194491829674261)
          ·
            refine ⟨2488847071616804515981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53095404194491829674261 2488847071616804515981)
            ·
              rfl

theorem cell19_73614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_73614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73614 prefixEnd_73614 := by exact prefixLift 73614
  have htrace : WordTrace (prefixWord ++ tailWord_73614) baseStart_73614 baseEnd_73614 := by
    simpa [prefixWord, tailWord_73614, baseEnd_73614] using wordTrace_append hprefix tailTrace_73614
  have hstable : (prefixWord ++ tailWord_73614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73614).length < 2 ^ (prefixWord ++ tailWord_73614).sum := by decide
  have hdescent : baseEnd_73614 < baseStart_73614 := by decide
  rcases family_descends (prefixWord ++ tailWord_73614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73633 : List Nat := [1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_73633 : Nat := 118140960795 + 73633 * 2 ^ 59
def prefixEnd_73633 : Nat := 4983230072969 + 3 ^ 40 * 73633 * 2
def baseEnd_73633 : Nat := 22405405056364826221555

theorem tailTrace_73633 : CollatzResearch.WordTrace tailWord_73633 prefixEnd_73633 22405405056364826221555 := by
  unfold tailWord_73633
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685616142247691360321553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1790410761498460906881035 2685616142247691360321553)
  ·
    refine ⟨2014212106685768520241165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2685616142247691360321553 2014212106685768520241165)
    ·
      refine ⟨755329540007163195090437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2014212106685768520241165 755329540007163195090437)
      ·
        refine ⟨141624288751343099079457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 755329540007163195090437 141624288751343099079457)
        ·
          refine ⟨106218216563507324309593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141624288751343099079457 106218216563507324309593)
          ·
            refine ⟨79663662422630493232195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106218216563507324309593 79663662422630493232195)
            ·
              refine ⟨119495493633945739848293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79663662422630493232195 119495493633945739848293)
              ·
                refine ⟨22405405056364826221555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119495493633945739848293 22405405056364826221555)
                ·
                  rfl

theorem cell19_73633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_73633 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73633 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73633 prefixEnd_73633 := by exact prefixLift 73633
  have htrace : WordTrace (prefixWord ++ tailWord_73633) baseStart_73633 baseEnd_73633 := by
    simpa [prefixWord, tailWord_73633, baseEnd_73633] using wordTrace_append hprefix tailTrace_73633
  have hstable : (prefixWord ++ tailWord_73633).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73633).length < 2 ^ (prefixWord ++ tailWord_73633).sum := by decide
  have hdescent : baseEnd_73633 < baseStart_73633 := by decide
  rcases family_descends (prefixWord ++ tailWord_73633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73709 : List Nat := [1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_73709 : Nat := 118140960795 + 73709 * 2 ^ 59
def prefixEnd_73709 : Nat := 4983230072969 + 3 ^ 40 * 73709 * 2
def baseEnd_73709 : Nat := 22428530703619168532459

theorem tailTrace_73709 : CollatzResearch.WordTrace tailWord_73709 prefixEnd_73709 22428530703619168532459 := by
  unfold tailWord_73709
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688388089972356340088181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1792258726648237560058787 2688388089972356340088181)
  ·
    refine ⟨252036383434908406883267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2688388089972356340088181 252036383434908406883267)
    ·
      refine ⟨378054575152362610324901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252036383434908406883267 378054575152362610324901)
      ·
        refine ⟨70885232841067989435919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 378054575152362610324901 70885232841067989435919)
        ·
          refine ⟨106327849261601984153879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70885232841067989435919 106327849261601984153879)
          ·
            refine ⟨159491773892402976230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106327849261601984153879 159491773892402976230819)
            ·
              refine ⟨239237660838604464346229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159491773892402976230819 239237660838604464346229)
              ·
                refine ⟨22428530703619168532459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239237660838604464346229 22428530703619168532459)
                ·
                  rfl

theorem cell19_73709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_73709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73709 prefixEnd_73709 := by exact prefixLift 73709
  have htrace : WordTrace (prefixWord ++ tailWord_73709) baseStart_73709 baseEnd_73709 := by
    simpa [prefixWord, tailWord_73709, baseEnd_73709] using wordTrace_append hprefix tailTrace_73709
  have hstable : (prefixWord ++ tailWord_73709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73709).length < 2 ^ (prefixWord ++ tailWord_73709).sum := by decide
  have hdescent : baseEnd_73709 < baseStart_73709 := by decide
  rcases family_descends (prefixWord ++ tailWord_73709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73749 : List Nat := [1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_73749 : Nat := 118140960795 + 73749 * 2 ^ 59
def prefixEnd_73749 : Nat := 4983230072969 + 3 ^ 40 * 73749 * 2
def baseEnd_73749 : Nat := 22440702096910927643461

theorem tailTrace_73749 : CollatzResearch.WordTrace tailWord_73749 prefixEnd_73749 22440702096910927643461 := by
  unfold tailWord_73749
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689847009827443171544301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1793231339884962114362867 2689847009827443171544301)
  ·
    refine ⟨1008692628685291189329113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2689847009827443171544301 1008692628685291189329113)
    ·
      refine ⟨756519471513968391996835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1008692628685291189329113 756519471513968391996835)
      ·
        refine ⟨1134779207270952587995253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756519471513968391996835 1134779207270952587995253)
        ·
          refine ⟨106385550681651805124555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1134779207270952587995253 106385550681651805124555)
          ·
            refine ⟨159578326022477707686833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106385550681651805124555 159578326022477707686833)
            ·
              refine ⟨119683744516858280765125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159578326022477707686833 119683744516858280765125)
              ·
                refine ⟨22440702096910927643461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119683744516858280765125 22440702096910927643461)
                ·
                  rfl

theorem cell19_73749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_73749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73749 prefixEnd_73749 := by exact prefixLift 73749
  have htrace : WordTrace (prefixWord ++ tailWord_73749) baseStart_73749 baseEnd_73749 := by
    simpa [prefixWord, tailWord_73749, baseEnd_73749] using wordTrace_append hprefix tailTrace_73749
  have hstable : (prefixWord ++ tailWord_73749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73749).length < 2 ^ (prefixWord ++ tailWord_73749).sum := by decide
  have hdescent : baseEnd_73749 < baseStart_73749 := by decide
  rcases family_descends (prefixWord ++ tailWord_73749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73806 : List Nat := [4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_73806 : Nat := 118140960795 + 73806 * 2 ^ 59
def prefixEnd_73806 : Nat := 4983230072969 + 3 ^ 40 * 73806 * 2
def baseEnd_73806 : Nat := 22458046332351684376639

theorem tailTrace_73806 : CollatzResearch.WordTrace tailWord_73806 prefixEnd_73806 22458046332351684376639 := by
  unfold tailWord_73806
  simp only [CollatzResearch.WordTrace]
  refine ⟨336490746327617738296159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1794617313747294604246181 336490746327617738296159)
  ·
    refine ⟨504736119491426607444239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 336490746327617738296159 504736119491426607444239)
    ·
      refine ⟨757104179237139911166359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504736119491426607444239 757104179237139911166359)
      ·
        refine ⟨1135656268855709866749539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757104179237139911166359 1135656268855709866749539)
        ·
          refine ⟨1703484403283564800124309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135656268855709866749539 1703484403283564800124309)
          ·
            refine ⟨79850831403917100005827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1703484403283564800124309 79850831403917100005827)
            ·
              refine ⟨119776247105875650008741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79850831403917100005827 119776247105875650008741)
              ·
                refine ⟨22458046332351684376639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119776247105875650008741 22458046332351684376639)
                ·
                  rfl

theorem cell19_73806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_73806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73806 prefixEnd_73806 := by exact prefixLift 73806
  have htrace : WordTrace (prefixWord ++ tailWord_73806) baseStart_73806 baseEnd_73806 := by
    simpa [prefixWord, tailWord_73806, baseEnd_73806] using wordTrace_append hprefix tailTrace_73806
  have hstable : (prefixWord ++ tailWord_73806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73806).length < 2 ^ (prefixWord ++ tailWord_73806).sum := by decide
  have hdescent : baseEnd_73806 < baseStart_73806 := by decide
  rcases family_descends (prefixWord ++ tailWord_73806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73876 : List Nat := [2, 4, 2, 3, 2, 1, 2, 3]
def baseStart_73876 : Nat := 118140960795 + 73876 * 2 ^ 59
def prefixEnd_73876 : Nat := 4983230072969 + 3 ^ 40 * 73876 * 2
def baseEnd_73876 : Nat := 22479346270612262820893

theorem tailTrace_73876 : CollatzResearch.WordTrace tailWord_73876 prefixEnd_73876 22479346270612262820893 := by
  unfold tailWord_73876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347239540183671930708741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1796319386911562574278321 1347239540183671930708741)
  ·
    refine ⟨252607413784438487007889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1347239540183671930708741 252607413784438487007889)
    ·
      refine ⟨189455560338328865255917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252607413784438487007889 189455560338328865255917)
      ·
        refine ⟨71045835126873324470969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189455560338328865255917 71045835126873324470969)
        ·
          refine ⟨53284376345154993353227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71045835126873324470969 53284376345154993353227)
          ·
            refine ⟨79926564517732490029841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53284376345154993353227 79926564517732490029841)
            ·
              refine ⟨59944923388299367522381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79926564517732490029841 59944923388299367522381)
              ·
                refine ⟨22479346270612262820893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59944923388299367522381 22479346270612262820893)
                ·
                  rfl

theorem cell19_73876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_73876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73876 prefixEnd_73876 := by exact prefixLift 73876
  have htrace : WordTrace (prefixWord ++ tailWord_73876) baseStart_73876 baseEnd_73876 := by
    simpa [prefixWord, tailWord_73876, baseEnd_73876] using wordTrace_append hprefix tailTrace_73876
  have hstable : (prefixWord ++ tailWord_73876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73876).length < 2 ^ (prefixWord ++ tailWord_73876).sum := by decide
  have hdescent : baseEnd_73876 < baseStart_73876 := by decide
  rcases family_descends (prefixWord ++ tailWord_73876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73880 : List Nat := [2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_73880 : Nat := 118140960795 + 73880 * 2 ^ 59
def prefixEnd_73880 : Nat := 4983230072969 + 3 ^ 40 * 73880 * 2
def baseEnd_73880 : Nat := 22480563409941438731993

theorem tailTrace_73880 : CollatzResearch.WordTrace tailWord_73880 prefixEnd_73880 22480563409941438731993 := by
  unfold tailWord_73880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347312486176426272281547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1796416648235235029708729 1347312486176426272281547)
  ·
    refine ⟨2020968729264639408422321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1347312486176426272281547 2020968729264639408422321)
    ·
      refine ⟨1515726546948479556316741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2020968729264639408422321 1515726546948479556316741)
      ·
        refine ⟨284198727552839916809389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1515726546948479556316741 284198727552839916809389)
        ·
          refine ⟨106574522832314968803521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284198727552839916809389 106574522832314968803521)
          ·
            refine ⟨79930892124236226602641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106574522832314968803521 79930892124236226602641)
            ·
              refine ⟨59948169093177169951981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79930892124236226602641 59948169093177169951981)
              ·
                refine ⟨22480563409941438731993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59948169093177169951981 22480563409941438731993)
                ·
                  rfl

theorem cell19_73880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_73880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73880 prefixEnd_73880 := by exact prefixLift 73880
  have htrace : WordTrace (prefixWord ++ tailWord_73880) baseStart_73880 baseEnd_73880 := by
    simpa [prefixWord, tailWord_73880, baseEnd_73880] using wordTrace_append hprefix tailTrace_73880
  have hstable : (prefixWord ++ tailWord_73880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73880).length < 2 ^ (prefixWord ++ tailWord_73880).sum := by decide
  have hdescent : baseEnd_73880 < baseStart_73880 := by decide
  rcases family_descends (prefixWord ++ tailWord_73880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73882 : List Nat := [3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_73882 : Nat := 118140960795 + 73882 * 2 ^ 59
def prefixEnd_73882 : Nat := 4983230072969 + 3 ^ 40 * 73882 * 2
def baseEnd_73882 : Nat := 22481171979606026687543

theorem tailTrace_73882 : CollatzResearch.WordTrace tailWord_73882 prefixEnd_73882 22481171979606026687543 := by
  unfold tailWord_73882
  simp only [CollatzResearch.WordTrace]
  refine ⟨673674479586401721533975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1796465278897071257423933 673674479586401721533975)
  ·
    refine ⟨1010511719379602582300963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673674479586401721533975 1010511719379602582300963)
    ·
      refine ⟨1515767579069403873451445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010511719379602582300963 1515767579069403873451445)
      ·
        refine ⟨142103210537756613136073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1515767579069403873451445 142103210537756613136073)
        ·
          refine ⟨106577407903317459852055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142103210537756613136073 106577407903317459852055)
          ·
            refine ⟨159866111854976189778083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106577407903317459852055 159866111854976189778083)
            ·
              refine ⟨239799167782464284667125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159866111854976189778083 239799167782464284667125)
              ·
                refine ⟨22481171979606026687543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239799167782464284667125 22481171979606026687543)
                ·
                  rfl

theorem cell19_73882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_73882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73882 prefixEnd_73882 := by exact prefixLift 73882
  have htrace : WordTrace (prefixWord ++ tailWord_73882) baseStart_73882 baseEnd_73882 := by
    simpa [prefixWord, tailWord_73882, baseEnd_73882] using wordTrace_append hprefix tailTrace_73882
  have hstable : (prefixWord ++ tailWord_73882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73882).length < 2 ^ (prefixWord ++ tailWord_73882).sum := by decide
  have hdescent : baseEnd_73882 < baseStart_73882 := by decide
  rcases family_descends (prefixWord ++ tailWord_73882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73884 : List Nat := [2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_73884 : Nat := 118140960795 + 73884 * 2 ^ 59
def prefixEnd_73884 : Nat := 4983230072969 + 3 ^ 40 * 73884 * 2
def baseEnd_73884 : Nat := 22481780549270614643093

theorem tailTrace_73884 : CollatzResearch.WordTrace tailWord_73884 prefixEnd_73884 22481780549270614643093 := by
  unfold tailWord_73884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347385432169180613854353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1796513909558907485139137 1347385432169180613854353)
  ·
    refine ⟨1010539074126885460390765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1347385432169180613854353 1010539074126885460390765)
    ·
      refine ⟨378952152797582047646537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1010539074126885460390765 378952152797582047646537)
      ·
        refine ⟨284214114598186535734903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378952152797582047646537 284214114598186535734903)
        ·
          refine ⟨426321171897279803602355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284214114598186535734903 426321171897279803602355)
          ·
            refine ⟨639481757845919705403533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426321171897279803602355 639481757845919705403533)
            ·
              refine ⟨239805659192219889526325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 639481757845919705403533 239805659192219889526325)
              ·
                refine ⟨22481780549270614643093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239805659192219889526325 22481780549270614643093)
                ·
                  rfl

theorem cell19_73884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_73884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73884 prefixEnd_73884 := by exact prefixLift 73884
  have htrace : WordTrace (prefixWord ++ tailWord_73884) baseStart_73884 baseEnd_73884 := by
    simpa [prefixWord, tailWord_73884, baseEnd_73884] using wordTrace_append hprefix tailTrace_73884
  have hstable : (prefixWord ++ tailWord_73884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73884).length < 2 ^ (prefixWord ++ tailWord_73884).sum := by decide
  have hdescent : baseEnd_73884 < baseStart_73884 := by decide
  rcases family_descends (prefixWord ++ tailWord_73884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73901 : List Nat := [1, 5, 2, 1, 2, 3, 5]
def baseStart_73901 : Nat := 118140960795 + 73901 * 2 ^ 59
def prefixEnd_73901 : Nat := 4983230072969 + 3 ^ 40 * 73901 * 2
def baseEnd_73901 : Nat := 7495651130473204088423

theorem tailTrace_73901 : CollatzResearch.WordTrace tailWord_73901 prefixEnd_73901 7495651130473204088423 := by
  unfold tailWord_73901
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695390905276773131077557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1796927270184515420718371 2695390905276773131077557)
  ·
    refine ⟨252692897369697481038521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2695390905276773131077557 252692897369697481038521)
    ·
      refine ⟨189519673027273110778891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252692897369697481038521 189519673027273110778891)
      ·
        refine ⟨284279509540909666168337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189519673027273110778891 284279509540909666168337)
        ·
          refine ⟨213209632155682249626253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284279509540909666168337 213209632155682249626253)
          ·
            refine ⟨79953612058380843609845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213209632155682249626253 79953612058380843609845)
            ·
              refine ⟨7495651130473204088423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79953612058380843609845 7495651130473204088423)
              ·
                rfl

theorem cell19_73901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_73901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73901 prefixEnd_73901 := by exact prefixLift 73901
  have htrace : WordTrace (prefixWord ++ tailWord_73901) baseStart_73901 baseEnd_73901 := by
    simpa [prefixWord, tailWord_73901, baseEnd_73901] using wordTrace_append hprefix tailTrace_73901
  have hstable : (prefixWord ++ tailWord_73901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73901).length < 2 ^ (prefixWord ++ tailWord_73901).sum := by decide
  have hdescent : baseEnd_73901 < baseStart_73901 := by decide
  rcases family_descends (prefixWord ++ tailWord_73901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73954 : List Nat := [3, 3, 4, 1, 2, 6]
def baseStart_73954 : Nat := 118140960795 + 73954 * 2 ^ 59
def prefixEnd_73954 : Nat := 4983230072969 + 3 ^ 40 * 73954 * 2
def baseEnd_73954 : Nat := 2500342276392354787483

theorem tailTrace_73954 : CollatzResearch.WordTrace tailWord_73954 prefixEnd_73954 2500342276392354787483 := by
  unfold tailWord_73954
  simp only [CollatzResearch.WordTrace]
  refine ⟨674330993521190795689229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1798215982723175455171277 674330993521190795689229)
  ·
    refine ⟨252874122570446548383461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 674330993521190795689229 252874122570446548383461)
    ·
      refine ⟨47413897981958727821899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252874122570446548383461 47413897981958727821899)
      ·
        refine ⟨71120846972938091732849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47413897981958727821899 71120846972938091732849)
        ·
          refine ⟨53340635229703568799637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71120846972938091732849 53340635229703568799637)
          ·
            refine ⟨2500342276392354787483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53340635229703568799637 2500342276392354787483)
            ·
              rfl

theorem cell19_73954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_73954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_73954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_73954 prefixEnd_73954 := by exact prefixLift 73954
  have htrace : WordTrace (prefixWord ++ tailWord_73954) baseStart_73954 baseEnd_73954 := by
    simpa [prefixWord, tailWord_73954, baseEnd_73954] using wordTrace_append hprefix tailTrace_73954
  have hstable : (prefixWord ++ tailWord_73954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73954).length < 2 ^ (prefixWord ++ tailWord_73954).sum := by decide
  have hdescent : baseEnd_73954 < baseStart_73954 := by decide
  rcases family_descends (prefixWord ++ tailWord_73954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74019 : List Nat := [1, 1, 1, 4, 2, 2, 8]
def baseStart_74019 : Nat := 118140960795 + 74019 * 2 ^ 59
def prefixEnd_74019 : Nat := 4983230072969 + 3 ^ 40 * 74019 * 2
def baseEnd_74019 : Nat := 7507619667210100547575

theorem tailTrace_74019 : CollatzResearch.WordTrace tailWord_74019 prefixEnd_74019 7507619667210100547575 := by
  unfold tailWord_74019
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699694718849279283873111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1799796479232852855915407 2699694718849279283873111)
  ·
    refine ⟨4049542078273918925809667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699694718849279283873111 4049542078273918925809667)
    ·
      refine ⟨6074313117410878388714501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049542078273918925809667 6074313117410878388714501)
      ·
        refine ⟨1138933709514539697883969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6074313117410878388714501 1138933709514539697883969)
        ·
          refine ⟨854200282135904773412977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138933709514539697883969 854200282135904773412977)
          ·
            refine ⟨640650211601928580059733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854200282135904773412977 640650211601928580059733)
            ·
              refine ⟨7507619667210100547575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 640650211601928580059733 7507619667210100547575)
              ·
                rfl

theorem cell19_74019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_74019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74019 prefixEnd_74019 := by exact prefixLift 74019
  have htrace : WordTrace (prefixWord ++ tailWord_74019) baseStart_74019 baseEnd_74019 := by
    simpa [prefixWord, tailWord_74019, baseEnd_74019] using wordTrace_append hprefix tailTrace_74019
  have hstable : (prefixWord ++ tailWord_74019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74019).length < 2 ^ (prefixWord ++ tailWord_74019).sum := by decide
  have hdescent : baseEnd_74019 < baseStart_74019 := by decide
  rcases family_descends (prefixWord ++ tailWord_74019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74049 : List Nat := [1, 2, 5, 2, 3, 1, 2, 3]
def baseStart_74049 : Nat := 118140960795 + 74049 * 2 ^ 59
def prefixEnd_74049 : Nat := 4983230072969 + 3 ^ 40 * 74049 * 2
def baseEnd_74049 : Nat := 22531987546599120975977

theorem tailTrace_74049 : CollatzResearch.WordTrace tailWord_74049 prefixEnd_74049 22531987546599120975977 := by
  unfold tailWord_74049
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700788908740594407465201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1800525939160396271643467 2700788908740594407465201)
  ·
    refine ⟨2025591681555445805598901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2700788908740594407465201 2025591681555445805598901)
    ·
      refine ⟨189899220145823044274897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2025591681555445805598901 189899220145823044274897)
      ·
        refine ⟨142424415109367283206173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189899220145823044274897 142424415109367283206173)
        ·
          refine ⟨53409155666012731202315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142424415109367283206173 53409155666012731202315)
          ·
            refine ⟨80113733499019096803473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53409155666012731202315 80113733499019096803473)
            ·
              refine ⟨60085300124264322602605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80113733499019096803473 60085300124264322602605)
              ·
                refine ⟨22531987546599120975977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60085300124264322602605 22531987546599120975977)
                ·
                  rfl

theorem cell19_74049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_74049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74049 prefixEnd_74049 := by exact prefixLift 74049
  have htrace : WordTrace (prefixWord ++ tailWord_74049) baseStart_74049 baseEnd_74049 := by
    simpa [prefixWord, tailWord_74049, baseEnd_74049] using wordTrace_append hprefix tailTrace_74049
  have hstable : (prefixWord ++ tailWord_74049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74049).length < 2 ^ (prefixWord ++ tailWord_74049).sum := by decide
  have hdescent : baseEnd_74049 < baseStart_74049 := by decide
  rcases family_descends (prefixWord ++ tailWord_74049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74093 : List Nat := [1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_74093 : Nat := 118140960795 + 74093 * 2 ^ 59
def prefixEnd_74093 : Nat := 4983230072969 + 3 ^ 40 * 74093 * 2
def baseEnd_74093 : Nat := 22545376079220055998079

theorem tailTrace_74093 : CollatzResearch.WordTrace tailWord_74093 prefixEnd_74093 22545376079220055998079 := by
  unfold tailWord_74093
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702393720581189922066933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1801595813720793281377955 2702393720581189922066933)
  ·
    refine ⟨253349411304486555193775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2702393720581189922066933 253349411304486555193775)
    ·
      refine ⟨380024116956729832790663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253349411304486555193775 380024116956729832790663)
      ·
        refine ⟨570036175435094749185995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380024116956729832790663 570036175435094749185995)
        ·
          refine ⟨855054263152642123778993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570036175435094749185995 855054263152642123778993)
          ·
            refine ⟨641290697364481592834245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855054263152642123778993 641290697364481592834245)
            ·
              refine ⟨120242005755840298656421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 641290697364481592834245 120242005755840298656421)
              ·
                refine ⟨22545376079220055998079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120242005755840298656421 22545376079220055998079)
                ·
                  rfl

theorem cell19_74093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_74093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74093 prefixEnd_74093 := by exact prefixLift 74093
  have htrace : WordTrace (prefixWord ++ tailWord_74093) baseStart_74093 baseEnd_74093 := by
    simpa [prefixWord, tailWord_74093, baseEnd_74093] using wordTrace_append hprefix tailTrace_74093
  have hstable : (prefixWord ++ tailWord_74093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74093).length < 2 ^ (prefixWord ++ tailWord_74093).sum := by decide
  have hdescent : baseEnd_74093 < baseStart_74093 := by decide
  rcases family_descends (prefixWord ++ tailWord_74093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74188 : List Nat := [2, 2, 1, 4, 3, 1, 6]
def baseStart_74188 : Nat := 118140960795 + 74188 * 2 ^ 59
def prefixEnd_74188 : Nat := 4983230072969 + 3 ^ 40 * 74188 * 2
def baseEnd_74188 : Nat := 7524761046095994628903

theorem tailTrace_74188 : CollatzResearch.WordTrace tailWord_74188 prefixEnd_74188 7524761046095994628903 := by
  unfold tailWord_74188
  simp only [CollatzResearch.WordTrace]
  refine ⟨1352929327618510573387609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1803905770158014097850145 1352929327618510573387609)
  ·
    refine ⟨1014696995713882930040707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1352929327618510573387609 1014696995713882930040707)
    ·
      refine ⟨1522045493570824395061061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014696995713882930040707 1522045493570824395061061)
      ·
        refine ⟨285383530044529574073949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1522045493570824395061061 285383530044529574073949)
        ·
          refine ⟨107018823766698590277731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285383530044529574073949 107018823766698590277731)
          ·
            refine ⟨160528235650047885416597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107018823766698590277731 160528235650047885416597)
            ·
              refine ⟨7524761046095994628903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160528235650047885416597 7524761046095994628903)
              ·
                rfl

theorem cell19_74188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_74188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74188 prefixEnd_74188 := by exact prefixLift 74188
  have htrace : WordTrace (prefixWord ++ tailWord_74188) baseStart_74188 baseEnd_74188 := by
    simpa [prefixWord, tailWord_74188, baseEnd_74188] using wordTrace_append hprefix tailTrace_74188
  have hstable : (prefixWord ++ tailWord_74188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74188).length < 2 ^ (prefixWord ++ tailWord_74188).sum := by decide
  have hdescent : baseEnd_74188 < baseStart_74188 := by decide
  rcases family_descends (prefixWord ++ tailWord_74188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74209 : List Nat := [1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_74209 : Nat := 118140960795 + 74209 * 2 ^ 59
def prefixEnd_74209 : Nat := 4983230072969 + 3 ^ 40 * 74209 * 2
def baseEnd_74209 : Nat := 22580673119766157419985

theorem tailTrace_74209 : CollatzResearch.WordTrace tailWord_74209 prefixEnd_74209 22580673119766157419985 := by
  unfold tailWord_74209
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706624588160941733289681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1804416392107294488859787 2706624588160941733289681)
  ·
    refine ⟨2029968441120706299967261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2706624588160941733289681 2029968441120706299967261)
    ·
      refine ⟨761238165420264862487723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2029968441120706299967261 761238165420264862487723)
      ·
        refine ⟨1141857248130397293731585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761238165420264862487723 1141857248130397293731585)
        ·
          refine ⟨856392936097797970298689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141857248130397293731585 856392936097797970298689)
          ·
            refine ⟨642294702073348477724017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856392936097797970298689 642294702073348477724017)
            ·
              refine ⟨481721026555011358293013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642294702073348477724017 481721026555011358293013)
              ·
                refine ⟨22580673119766157419985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481721026555011358293013 22580673119766157419985)
                ·
                  rfl

theorem cell19_74209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_74209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74209 prefixEnd_74209 := by exact prefixLift 74209
  have htrace : WordTrace (prefixWord ++ tailWord_74209) baseStart_74209 baseEnd_74209 := by
    simpa [prefixWord, tailWord_74209, baseEnd_74209] using wordTrace_append hprefix tailTrace_74209
  have hstable : (prefixWord ++ tailWord_74209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74209).length < 2 ^ (prefixWord ++ tailWord_74209).sum := by decide
  have hdescent : baseEnd_74209 < baseStart_74209 := by decide
  rcases family_descends (prefixWord ++ tailWord_74209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74264 : List Nat := [2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_74264 : Nat := 118140960795 + 74264 * 2 ^ 59
def prefixEnd_74264 : Nat := 4983230072969 + 3 ^ 40 * 74264 * 2
def baseEnd_74264 : Nat := 22597408785542326197613

theorem tailTrace_74264 : CollatzResearch.WordTrace tailWord_74264 prefixEnd_74264 22597408785542326197613 := by
  unfold tailWord_74264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354315301480843063270923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1805753735307790751027897 1354315301480843063270923)
  ·
    refine ⟨2031472952221264594906385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354315301480843063270923 2031472952221264594906385)
    ·
      refine ⟨1523604714165948446179789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2031472952221264594906385 1523604714165948446179789)
      ·
        refine ⟨571351767812230667317421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1523604714165948446179789 571351767812230667317421)
        ·
          refine ⟨214256912929586500244033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 571351767812230667317421 214256912929586500244033)
          ·
            refine ⟨160692684697189875183025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214256912929586500244033 160692684697189875183025)
            ·
              refine ⟨120519513522892406387269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160692684697189875183025 120519513522892406387269)
              ·
                refine ⟨22597408785542326197613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120519513522892406387269 22597408785542326197613)
                ·
                  rfl

theorem cell19_74264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_74264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74264 prefixEnd_74264 := by exact prefixLift 74264
  have htrace : WordTrace (prefixWord ++ tailWord_74264) baseStart_74264 baseEnd_74264 := by
    simpa [prefixWord, tailWord_74264, baseEnd_74264] using wordTrace_append hprefix tailTrace_74264
  have hstable : (prefixWord ++ tailWord_74264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74264).length < 2 ^ (prefixWord ++ tailWord_74264).sum := by decide
  have hdescent : baseEnd_74264 < baseStart_74264 := by decide
  rcases family_descends (prefixWord ++ tailWord_74264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74266 : List Nat := [3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_74266 : Nat := 118140960795 + 74266 * 2 ^ 59
def prefixEnd_74266 : Nat := 4983230072969 + 3 ^ 40 * 74266 * 2
def baseEnd_74266 : Nat := 22598017355206914153163

theorem tailTrace_74266 : CollatzResearch.WordTrace tailWord_74266 prefixEnd_74266 22598017355206914153163 := by
  unfold tailWord_74266
  simp only [CollatzResearch.WordTrace]
  refine ⟨677175887238610117028663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1805802365969626978743101 677175887238610117028663)
  ·
    refine ⟨1015763830857915175542995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 677175887238610117028663 1015763830857915175542995)
    ·
      refine ⟨1523645746286872763314493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015763830857915175542995 1523645746286872763314493)
      ·
        refine ⟨571367154857577286242935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1523645746286872763314493 571367154857577286242935)
        ·
          refine ⟨857050732286365929364403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571367154857577286242935 857050732286365929364403)
          ·
            refine ⟨1285576098429548894046605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857050732286365929364403 1285576098429548894046605)
            ·
              refine ⟨482091036911080835267477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285576098429548894046605 482091036911080835267477)
              ·
                refine ⟨22598017355206914153163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 482091036911080835267477 22598017355206914153163)
                ·
                  rfl

theorem cell19_74266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_74266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74266 prefixEnd_74266 := by exact prefixLift 74266
  have htrace : WordTrace (prefixWord ++ tailWord_74266) baseStart_74266 baseEnd_74266 := by
    simpa [prefixWord, tailWord_74266, baseEnd_74266] using wordTrace_append hprefix tailTrace_74266
  have hstable : (prefixWord ++ tailWord_74266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74266).length < 2 ^ (prefixWord ++ tailWord_74266).sum := by decide
  have hdescent : baseEnd_74266 < baseStart_74266 := by decide
  rcases family_descends (prefixWord ++ tailWord_74266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74302 : List Nat := [4, 2, 1, 4, 8]
def baseStart_74302 : Nat := 118140960795 + 74302 * 2 ^ 59
def prefixEnd_74302 : Nat := 4983230072969 + 3 ^ 40 * 74302 * 2
def baseEnd_74302 : Nat := 837369318858129531595

theorem tailTrace_74302 : CollatzResearch.WordTrace tailWord_74302 prefixEnd_74302 837369318858129531595 := by
  unfold tailWord_74302
  simp only [CollatzResearch.WordTrace]
  refine ⟨338752072103002327053145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1806677717882679077616773 338752072103002327053145)
  ·
    refine ⟨254064054077251745289859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 338752072103002327053145 254064054077251745289859)
    ·
      refine ⟨381096081115877617934789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254064054077251745289859 381096081115877617934789)
      ·
        refine ⟨71455515209227053362773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381096081115877617934789 71455515209227053362773)
        ·
          refine ⟨837369318858129531595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 71455515209227053362773 837369318858129531595)
          ·
            rfl

theorem cell19_74302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 8].length) (baseStart_74302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74302 prefixEnd_74302 := by exact prefixLift 74302
  have htrace : WordTrace (prefixWord ++ tailWord_74302) baseStart_74302 baseEnd_74302 := by
    simpa [prefixWord, tailWord_74302, baseEnd_74302] using wordTrace_append hprefix tailTrace_74302
  have hstable : (prefixWord ++ tailWord_74302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74302).length < 2 ^ (prefixWord ++ tailWord_74302).sum := by decide
  have hdescent : baseEnd_74302 < baseStart_74302 := by decide
  rcases family_descends (prefixWord ++ tailWord_74302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74321 : List Nat := [1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_74321 : Nat := 118140960795 + 74321 * 2 ^ 59
def prefixEnd_74321 : Nat := 4983230072969 + 3 ^ 40 * 74321 * 2
def baseEnd_74321 : Nat := 22614753020983082930791

theorem tailTrace_74321 : CollatzResearch.WordTrace tailWord_74321 prefixEnd_74321 22614753020983082930791 := by
  unfold tailWord_74321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710709563755184861366817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1807139709170123240911211 2710709563755184861366817)
  ·
    refine ⟨2033032172816388646025113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2710709563755184861366817 2033032172816388646025113)
    ·
      refine ⟨1524774129612291484518835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2033032172816388646025113 1524774129612291484518835)
      ·
        refine ⟨2287161194418437226778253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524774129612291484518835 2287161194418437226778253)
        ·
          refine ⟨857685447906913960041845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2287161194418437226778253 857685447906913960041845)
          ·
            refine ⟨80408010741273183753923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 857685447906913960041845 80408010741273183753923)
            ·
              refine ⟨120612016111909775630885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80408010741273183753923 120612016111909775630885)
              ·
                refine ⟨22614753020983082930791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120612016111909775630885 22614753020983082930791)
                ·
                  rfl

theorem cell19_74321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_74321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74321 prefixEnd_74321 := by exact prefixLift 74321
  have htrace : WordTrace (prefixWord ++ tailWord_74321) baseStart_74321 baseEnd_74321 := by
    simpa [prefixWord, tailWord_74321, baseEnd_74321] using wordTrace_append hprefix tailTrace_74321
  have hstable : (prefixWord ++ tailWord_74321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74321).length < 2 ^ (prefixWord ++ tailWord_74321).sum := by decide
  have hdescent : baseEnd_74321 < baseStart_74321 := by decide
  rcases family_descends (prefixWord ++ tailWord_74321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74340 : List Nat := [2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_74340 : Nat := 118140960795 + 74340 * 2 ^ 59
def prefixEnd_74340 : Nat := 4983230072969 + 3 ^ 40 * 74340 * 2
def baseEnd_74340 : Nat := 22620534432796668508517

theorem tailTrace_74340 : CollatzResearch.WordTrace tailWord_74340 prefixEnd_74340 22620534432796668508517 := by
  unfold tailWord_74340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355701275343175553154237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1807601700457567404205649 1355701275343175553154237)
  ·
    refine ⟨508387978253690832432839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1355701275343175553154237 508387978253690832432839)
    ·
      refine ⟨762581967380536248649259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508387978253690832432839 762581967380536248649259)
      ·
        refine ⟨1143872951070804372973889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762581967380536248649259 1143872951070804372973889)
        ·
          refine ⟨857904713303103279730417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1143872951070804372973889 857904713303103279730417)
          ·
            refine ⟨643428534977327459797813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857904713303103279730417 643428534977327459797813)
            ·
              refine ⟨60321425154124449356045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 643428534977327459797813 60321425154124449356045)
              ·
                refine ⟨22620534432796668508517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60321425154124449356045 22620534432796668508517)
                ·
                  rfl

theorem cell19_74340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_74340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74340 prefixEnd_74340 := by exact prefixLift 74340
  have htrace : WordTrace (prefixWord ++ tailWord_74340) baseStart_74340 baseEnd_74340 := by
    simpa [prefixWord, tailWord_74340, baseEnd_74340] using wordTrace_append hprefix tailTrace_74340
  have hstable : (prefixWord ++ tailWord_74340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74340).length < 2 ^ (prefixWord ++ tailWord_74340).sum := by decide
  have hdescent : baseEnd_74340 < baseStart_74340 := by decide
  rcases family_descends (prefixWord ++ tailWord_74340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74361 : List Nat := [1, 2, 1, 3, 3, 3, 6]
def baseStart_74361 : Nat := 118140960795 + 74361 * 2 ^ 59
def prefixEnd_74361 : Nat := 4983230072969 + 3 ^ 40 * 74361 * 2
def baseEnd_74361 : Nat := 7542308138091614013931

theorem tailTrace_74361 : CollatzResearch.WordTrace tailWord_74361 prefixEnd_74361 7542308138091614013931 := by
  unfold tailWord_74361
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712168483610271692822937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1808112322406847795215291 2712168483610271692822937)
  ·
    refine ⟨2034126362707703769617203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2712168483610271692822937 2034126362707703769617203)
    ·
      refine ⟨3051189544061555654425805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034126362707703769617203 3051189544061555654425805)
      ·
        refine ⟨1144196079023083370409677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3051189544061555654425805 1144196079023083370409677)
        ·
          refine ⟨429073529633656263903629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1144196079023083370409677 429073529633656263903629)
          ·
            refine ⟨160902573612621098963861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429073529633656263903629 160902573612621098963861)
            ·
              refine ⟨7542308138091614013931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160902573612621098963861 7542308138091614013931)
              ·
                rfl

theorem cell19_74361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_74361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74361 prefixEnd_74361 := by exact prefixLift 74361
  have htrace : WordTrace (prefixWord ++ tailWord_74361) baseStart_74361 baseEnd_74361 := by
    simpa [prefixWord, tailWord_74361, baseEnd_74361] using wordTrace_append hprefix tailTrace_74361
  have hstable : (prefixWord ++ tailWord_74361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74361).length < 2 ^ (prefixWord ++ tailWord_74361).sum := by decide
  have hdescent : baseEnd_74361 < baseStart_74361 := by decide
  rcases family_descends (prefixWord ++ tailWord_74361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74397 : List Nat := [1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_74397 : Nat := 118140960795 + 74397 * 2 ^ 59
def prefixEnd_74397 : Nat := 4983230072969 + 3 ^ 40 * 74397 * 2
def baseEnd_74397 : Nat := 22637878668237425241695

theorem tailTrace_74397 : CollatzResearch.WordTrace tailWord_74397 prefixEnd_74397 22637878668237425241695 := by
  unfold tailWord_74397
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713481511479849841133445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1808987674319899894088963 2713481511479849841133445)
  ·
    refine ⟨508777783402471845212521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2713481511479849841133445 508777783402471845212521)
    ·
      refine ⟨381583337551853883909391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 508777783402471845212521 381583337551853883909391)
      ·
        refine ⟨572375006327780825864087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381583337551853883909391 572375006327780825864087)
        ·
          refine ⟨858562509491671238796131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572375006327780825864087 858562509491671238796131)
          ·
            refine ⟨1287843764237506858194197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858562509491671238796131 1287843764237506858194197)
            ·
              refine ⟨60367676448633133977853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1287843764237506858194197 60367676448633133977853)
              ·
                refine ⟨22637878668237425241695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60367676448633133977853 22637878668237425241695)
                ·
                  rfl

theorem cell19_74397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_74397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74397 prefixEnd_74397 := by exact prefixLift 74397
  have htrace : WordTrace (prefixWord ++ tailWord_74397) baseStart_74397 baseEnd_74397 := by
    simpa [prefixWord, tailWord_74397, baseEnd_74397] using wordTrace_append hprefix tailTrace_74397
  have hstable : (prefixWord ++ tailWord_74397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74397).length < 2 ^ (prefixWord ++ tailWord_74397).sum := by decide
  have hdescent : baseEnd_74397 < baseStart_74397 := by decide
  rcases family_descends (prefixWord ++ tailWord_74397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74414 : List Nat := [4, 1, 4, 1, 1, 3, 5]
def baseStart_74414 : Nat := 118140960795 + 74414 * 2 ^ 59
def prefixEnd_74414 : Nat := 4983230072969 + 3 ^ 40 * 74414 * 2
def baseEnd_74414 : Nat := 7547683836795474287957

theorem tailTrace_74414 : CollatzResearch.WordTrace tailWord_74414 prefixEnd_74414 7547683836795474287957 := by
  unfold tailWord_74414
  simp only [CollatzResearch.WordTrace]
  refine ⟨339262694052282718062787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1809401034945507829668197 339262694052282718062787)
  ·
    refine ⟨508894041078424077094181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 339262694052282718062787 508894041078424077094181)
    ·
      refine ⟨95417632702204514455159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 508894041078424077094181 95417632702204514455159)
      ·
        refine ⟨143126449053306771682739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95417632702204514455159 143126449053306771682739)
        ·
          refine ⟨214689673579960157524109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143126449053306771682739 214689673579960157524109)
          ·
            refine ⟨80508627592485059071541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214689673579960157524109 80508627592485059071541)
            ·
              refine ⟨7547683836795474287957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80508627592485059071541 7547683836795474287957)
              ·
                rfl

theorem cell19_74414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_74414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74414 prefixEnd_74414 := by exact prefixLift 74414
  have htrace : WordTrace (prefixWord ++ tailWord_74414) baseStart_74414 baseEnd_74414 := by
    simpa [prefixWord, tailWord_74414, baseEnd_74414] using wordTrace_append hprefix tailTrace_74414
  have hstable : (prefixWord ++ tailWord_74414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74414).length < 2 ^ (prefixWord ++ tailWord_74414).sum := by decide
  have hdescent : baseEnd_74414 < baseStart_74414 := by decide
  rcases family_descends (prefixWord ++ tailWord_74414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74456 : List Nat := [2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_74456 : Nat := 118140960795 + 74456 * 2 ^ 59
def prefixEnd_74456 : Nat := 4983230072969 + 3 ^ 40 * 74456 * 2
def baseEnd_74456 : Nat := 22655831473342769930423

theorem tailTrace_74456 : CollatzResearch.WordTrace tailWord_74456 prefixEnd_74456 22655831473342769930423 := by
  unfold tailWord_74456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357816709133051458765611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1810422278844068611687481 1357816709133051458765611)
  ·
    refine ⟨2036725063699577188148417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357816709133051458765611 2036725063699577188148417)
    ·
      refine ⟨1527543797774682891111313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036725063699577188148417 1527543797774682891111313)
      ·
        refine ⟨1145657848331012168333485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1527543797774682891111313 1145657848331012168333485)
        ·
          refine ⟨429621693124129563125057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1145657848331012168333485 429621693124129563125057)
          ·
            refine ⟨322216269843097172343793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429621693124129563125057 322216269843097172343793)
            ·
              refine ⟨241662202382322879257845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322216269843097172343793 241662202382322879257845)
              ·
                refine ⟨22655831473342769930423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241662202382322879257845 22655831473342769930423)
                ·
                  rfl

theorem cell19_74456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_74456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74456 prefixEnd_74456 := by exact prefixLift 74456
  have htrace : WordTrace (prefixWord ++ tailWord_74456) baseStart_74456 baseEnd_74456 := by
    simpa [prefixWord, tailWord_74456, baseEnd_74456] using wordTrace_append hprefix tailTrace_74456
  have hstable : (prefixWord ++ tailWord_74456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74456).length < 2 ^ (prefixWord ++ tailWord_74456).sum := by decide
  have hdescent : baseEnd_74456 < baseStart_74456 := by decide
  rcases family_descends (prefixWord ++ tailWord_74456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74492 : List Nat := [2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_74492 : Nat := 118140960795 + 74492 * 2 ^ 59
def prefixEnd_74492 : Nat := 4983230072969 + 3 ^ 40 * 74492 * 2
def baseEnd_74492 : Nat := 22666785727305353130325

theorem tailTrace_74492 : CollatzResearch.WordTrace tailWord_74492 prefixEnd_74492 22666785727305353130325 := by
  unfold tailWord_74492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358473223067840532920865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1811297630757120710561153 1358473223067840532920865)
  ·
    refine ⟨1018854917300880399690649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1358473223067840532920865 1018854917300880399690649)
    ·
      refine ⟨764141187975660299767987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1018854917300880399690649 764141187975660299767987)
      ·
        refine ⟨1146211781963490449651981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764141187975660299767987 1146211781963490449651981)
        ·
          refine ⟨429829418236308918619493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1146211781963490449651981 429829418236308918619493)
          ·
            refine ⟨80593015919307922241155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 429829418236308918619493 80593015919307922241155)
            ·
              refine ⟨120889523878961883361733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80593015919307922241155 120889523878961883361733)
              ·
                refine ⟨22666785727305353130325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120889523878961883361733 22666785727305353130325)
                ·
                  rfl

theorem cell19_74492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_74492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74492 prefixEnd_74492 := by exact prefixLift 74492
  have htrace : WordTrace (prefixWord ++ tailWord_74492) baseStart_74492 baseEnd_74492 := by
    simpa [prefixWord, tailWord_74492, baseEnd_74492] using wordTrace_append hprefix tailTrace_74492
  have hstable : (prefixWord ++ tailWord_74492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74492).length < 2 ^ (prefixWord ++ tailWord_74492).sum := by decide
  have hdescent : baseEnd_74492 < baseStart_74492 := by decide
  rcases family_descends (prefixWord ++ tailWord_74492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74648 : List Nat := [2, 1, 2, 14]
def baseStart_74648 : Nat := 118140960795 + 74648 * 2 ^ 59
def prefixEnd_74648 : Nat := 4983230072969 + 3 ^ 40 * 74648 * 2
def baseEnd_74648 : Nat := 280422890878311279793

theorem tailTrace_74648 : CollatzResearch.WordTrace tailWord_74648 prefixEnd_74648 280422890878311279793 := by
  unfold tailWord_74648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361318116785259854260299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1815090822380346472347065 1361318116785259854260299)
  ·
    refine ⟨2041977175177889781390449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361318116785259854260299 2041977175177889781390449)
    ·
      refine ⟨1531482881383417336042837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2041977175177889781390449 1531482881383417336042837)
      ·
        refine ⟨280422890878311279793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1531482881383417336042837 280422890878311279793)
        ·
          rfl

theorem cell19_74648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 14].length) (baseStart_74648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74648 prefixEnd_74648 := by exact prefixLift 74648
  have htrace : WordTrace (prefixWord ++ tailWord_74648) baseStart_74648 baseEnd_74648 := by
    simpa [prefixWord, tailWord_74648, baseEnd_74648] using wordTrace_append hprefix tailTrace_74648
  have hstable : (prefixWord ++ tailWord_74648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74648).length < 2 ^ (prefixWord ++ tailWord_74648).sum := by decide
  have hdescent : baseEnd_74648 < baseStart_74648 := by decide
  rcases family_descends (prefixWord ++ tailWord_74648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74705 : List Nat := [1, 2, 2, 1, 2, 1, 10]
def baseStart_74705 : Nat := 118140960795 + 74705 * 2 ^ 59
def prefixEnd_74705 : Nat := 4983230072969 + 3 ^ 40 * 74705 * 2
def baseEnd_74705 : Nat := 7577199465527990132137

theorem tailTrace_74705 : CollatzResearch.WordTrace tailWord_74705 prefixEnd_74705 7577199465527990132137 := by
  unfold tailWord_74705
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724715194364018443345569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1816476796242678962230379 2724715194364018443345569)
  ·
    refine ⟨2043536395773013832509177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2724715194364018443345569 2043536395773013832509177)
    ·
      refine ⟨1532652296829760374381883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2043536395773013832509177 1532652296829760374381883)
      ·
        refine ⟨2298978445244640561572825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532652296829760374381883 2298978445244640561572825)
        ·
          refine ⟨1724233833933480421179619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298978445244640561572825 1724233833933480421179619)
          ·
            refine ⟨2586350750900220631769429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724233833933480421179619 2586350750900220631769429)
            ·
              refine ⟨7577199465527990132137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2586350750900220631769429 7577199465527990132137)
              ·
                rfl

theorem cell19_74705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_74705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74705 prefixEnd_74705 := by exact prefixLift 74705
  have htrace : WordTrace (prefixWord ++ tailWord_74705) baseStart_74705 baseEnd_74705 := by
    simpa [prefixWord, tailWord_74705, baseEnd_74705] using wordTrace_append hprefix tailTrace_74705
  have hstable : (prefixWord ++ tailWord_74705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74705).length < 2 ^ (prefixWord ++ tailWord_74705).sum := by decide
  have hdescent : baseEnd_74705 < baseStart_74705 := by decide
  rcases family_descends (prefixWord ++ tailWord_74705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74754 : List Nat := [3, 4, 1, 3, 2, 1, 5]
def baseStart_74754 : Nat := 118140960795 + 74754 * 2 ^ 59
def prefixEnd_74754 : Nat := 4983230072969 + 3 ^ 40 * 74754 * 2
def baseEnd_74754 : Nat := 7582169451122125102463

theorem tailTrace_74754 : CollatzResearch.WordTrace tailWord_74754 prefixEnd_74754 7582169451122125102463 := by
  unfold tailWord_74754
  simp only [CollatzResearch.WordTrace]
  refine ⟨681625592796624952969829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1817668247457666541252877 681625592796624952969829)
  ·
    refine ⟨127804798649367178681843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 681625592796624952969829 127804798649367178681843)
    ·
      refine ⟨191707197974050768022765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127804798649367178681843 191707197974050768022765)
      ·
        refine ⟨71890199240269038008537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191707197974050768022765 71890199240269038008537)
        ·
          refine ⟨53917649430201778506403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71890199240269038008537 53917649430201778506403)
          ·
            refine ⟨80876474145302667759605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53917649430201778506403 80876474145302667759605)
            ·
              refine ⟨7582169451122125102463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80876474145302667759605 7582169451122125102463)
              ·
                rfl

theorem cell19_74754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_74754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74754 prefixEnd_74754 := by exact prefixLift 74754
  have htrace : WordTrace (prefixWord ++ tailWord_74754) baseStart_74754 baseEnd_74754 := by
    simpa [prefixWord, tailWord_74754, baseEnd_74754] using wordTrace_append hprefix tailTrace_74754
  have hstable : (prefixWord ++ tailWord_74754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74754).length < 2 ^ (prefixWord ++ tailWord_74754).sum := by decide
  have hdescent : baseEnd_74754 < baseStart_74754 := by decide
  rcases family_descends (prefixWord ++ tailWord_74754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74760 : List Nat := [2, 1, 3, 2, 1, 5, 5]
def baseStart_74760 : Nat := 118140960795 + 74760 * 2 ^ 59
def prefixEnd_74760 : Nat := 4983230072969 + 3 ^ 40 * 74760 * 2
def baseEnd_74760 : Nat := 7582778020786713058013

theorem tailTrace_74760 : CollatzResearch.WordTrace tailWord_74760 prefixEnd_74760 7582778020786713058013 := by
  unfold tailWord_74760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363360604582381418298867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1817814139443175224398489 1363360604582381418298867)
  ·
    refine ⟨2045040906873572127448301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1363360604582381418298867 2045040906873572127448301)
    ·
      refine ⟨766890340077589547793113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2045040906873572127448301 766890340077589547793113)
      ·
        refine ⟨575167755058192160844835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 766890340077589547793113 575167755058192160844835)
        ·
          refine ⟨862751632587288241267253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575167755058192160844835 862751632587288241267253)
          ·
            refine ⟨80882965555058272618805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 862751632587288241267253 80882965555058272618805)
            ·
              refine ⟨7582778020786713058013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80882965555058272618805 7582778020786713058013)
              ·
                rfl

theorem cell19_74760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_74760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74760 prefixEnd_74760 := by exact prefixLift 74760
  have htrace : WordTrace (prefixWord ++ tailWord_74760) baseStart_74760 baseEnd_74760 := by
    simpa [prefixWord, tailWord_74760, baseEnd_74760] using wordTrace_append hprefix tailTrace_74760
  have hstable : (prefixWord ++ tailWord_74760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74760).length < 2 ^ (prefixWord ++ tailWord_74760).sum := by decide
  have hdescent : baseEnd_74760 < baseStart_74760 := by decide
  rcases family_descends (prefixWord ++ tailWord_74760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74798 : List Nat := [4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_74798 : Nat := 118140960795 + 74798 * 2 ^ 59
def prefixEnd_74798 : Nat := 4983230072969 + 3 ^ 40 * 74798 * 2
def baseEnd_74798 : Nat := 22759896885987310329491

theorem tailTrace_74798 : CollatzResearch.WordTrace tailWord_74798 prefixEnd_74798 22759896885987310329491 := by
  unfold tailWord_74798
  simp only [CollatzResearch.WordTrace]
  refine ⟨341013397878386915810131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1818738122018063550987365 341013397878386915810131)
  ·
    refine ⟨511520096817580373715197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 341013397878386915810131 511520096817580373715197)
    ·
      refine ⟨191820036306592640143199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 511520096817580373715197 191820036306592640143199)
      ·
        refine ⟨287730054459888960214799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191820036306592640143199 287730054459888960214799)
        ·
          refine ⟨431595081689833440322199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287730054459888960214799 431595081689833440322199)
          ·
            refine ⟨647392622534750160483299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431595081689833440322199 647392622534750160483299)
            ·
              refine ⟨971088933802125240724949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647392622534750160483299 971088933802125240724949)
              ·
                refine ⟨22759896885987310329491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 971088933802125240724949 22759896885987310329491)
                ·
                  rfl

theorem cell19_74798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_74798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74798 prefixEnd_74798 := by exact prefixLift 74798
  have htrace : WordTrace (prefixWord ++ tailWord_74798) baseStart_74798 baseEnd_74798 := by
    simpa [prefixWord, tailWord_74798, baseEnd_74798] using wordTrace_append hprefix tailTrace_74798
  have hstable : (prefixWord ++ tailWord_74798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74798).length < 2 ^ (prefixWord ++ tailWord_74798).sum := by decide
  have hdescent : baseEnd_74798 < baseStart_74798 := by decide
  rcases family_descends (prefixWord ++ tailWord_74798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74800 : List Nat := [2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_74800 : Nat := 118140960795 + 74800 * 2 ^ 59
def prefixEnd_74800 : Nat := 4983230072969 + 3 ^ 40 * 74800 * 2
def baseEnd_74800 : Nat := 22760505455651898285041

theorem tailTrace_74800 : CollatzResearch.WordTrace tailWord_74800 prefixEnd_74800 22760505455651898285041 := by
  unfold tailWord_74800
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364090064509924834026927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1818786752679899778702569 1364090064509924834026927)
  ·
    refine ⟨2046135096764887251040391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364090064509924834026927 2046135096764887251040391)
    ·
      refine ⟨3069202645147330876560587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046135096764887251040391 3069202645147330876560587)
      ·
        refine ⟨4603803967720996314840881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3069202645147330876560587 4603803967720996314840881)
        ·
          refine ⟨3452852975790747236130661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603803967720996314840881 3452852975790747236130661)
          ·
            refine ⟨647409932960765106774499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3452852975790747236130661 647409932960765106774499)
            ·
              refine ⟨971114899441147660161749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647409932960765106774499 971114899441147660161749)
              ·
                refine ⟨22760505455651898285041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 971114899441147660161749 22760505455651898285041)
                ·
                  rfl

theorem cell19_74800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_74800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74800 prefixEnd_74800 := by exact prefixLift 74800
  have htrace : WordTrace (prefixWord ++ tailWord_74800) baseStart_74800 baseEnd_74800 := by
    simpa [prefixWord, tailWord_74800, baseEnd_74800] using wordTrace_append hprefix tailTrace_74800
  have hstable : (prefixWord ++ tailWord_74800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74800).length < 2 ^ (prefixWord ++ tailWord_74800).sum := by decide
  have hdescent : baseEnd_74800 < baseStart_74800 := by decide
  rcases family_descends (prefixWord ++ tailWord_74800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74817 : List Nat := [1, 2, 5, 1, 3, 7]
def baseStart_74817 : Nat := 118140960795 + 74817 * 2 ^ 59
def prefixEnd_74817 : Nat := 4983230072969 + 3 ^ 40 * 74817 * 2
def baseEnd_74817 : Nat := 2529519810866766211913

theorem tailTrace_74817 : CollatzResearch.WordTrace tailWord_74817 prefixEnd_74817 2529519810866766211913 := by
  unfold tailWord_74817
  simp only [CollatzResearch.WordTrace]
  refine ⟨2728800169958261571422705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1819200113305507714281803 2728800169958261571422705)
  ·
    refine ⟨2046600127468696178567029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2728800169958261571422705 2046600127468696178567029)
    ·
      refine ⟨191868761950190266740659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2046600127468696178567029 191868761950190266740659)
      ·
        refine ⟨287803142925285400110989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191868761950190266740659 287803142925285400110989)
        ·
          refine ⟨107926178596982025041621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287803142925285400110989 107926178596982025041621)
          ·
            refine ⟨2529519810866766211913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 107926178596982025041621 2529519810866766211913)
            ·
              rfl

theorem cell19_74817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_74817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74817 prefixEnd_74817 := by exact prefixLift 74817
  have htrace : WordTrace (prefixWord ++ tailWord_74817) baseStart_74817 baseEnd_74817 := by
    simpa [prefixWord, tailWord_74817, baseEnd_74817] using wordTrace_append hprefix tailTrace_74817
  have hstable : (prefixWord ++ tailWord_74817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74817).length < 2 ^ (prefixWord ++ tailWord_74817).sum := by decide
  have hdescent : baseEnd_74817 < baseStart_74817 := by decide
  rcases family_descends (prefixWord ++ tailWord_74817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74834 : List Nat := [3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_74834 : Nat := 118140960795 + 74834 * 2 ^ 59
def prefixEnd_74834 : Nat := 4983230072969 + 3 ^ 40 * 74834 * 2
def baseEnd_74834 : Nat := 22770851139949893529393

theorem tailTrace_74834 : CollatzResearch.WordTrace tailWord_74834 prefixEnd_74834 22770851139949893529393 := by
  unfold tailWord_74834
  simp only [CollatzResearch.WordTrace]
  refine ⟨682355052724168368697889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1819613473931115649861037 682355052724168368697889)
  ·
    refine ⟨511766289543126276523417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 682355052724168368697889 511766289543126276523417)
    ·
      refine ⟨383824717157344707392563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 511766289543126276523417 383824717157344707392563)
      ·
        refine ⟨575737075736017061088845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383824717157344707392563 575737075736017061088845)
        ·
          refine ⟨215901403401006397908317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 575737075736017061088845 215901403401006397908317)
          ·
            refine ⟨80963026275377399215619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215901403401006397908317 80963026275377399215619)
            ·
              refine ⟨121444539413066098823429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80963026275377399215619 121444539413066098823429)
              ·
                refine ⟨22770851139949893529393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121444539413066098823429 22770851139949893529393)
                ·
                  rfl

theorem cell19_74834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_74834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74834 prefixEnd_74834 := by exact prefixLift 74834
  have htrace : WordTrace (prefixWord ++ tailWord_74834) baseStart_74834 baseEnd_74834 := by
    simpa [prefixWord, tailWord_74834, baseEnd_74834] using wordTrace_append hprefix tailTrace_74834
  have hstable : (prefixWord ++ tailWord_74834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74834).length < 2 ^ (prefixWord ++ tailWord_74834).sum := by decide
  have hdescent : baseEnd_74834 < baseStart_74834 := by decide
  rcases family_descends (prefixWord ++ tailWord_74834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74836 : List Nat := [2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_74836 : Nat := 118140960795 + 74836 * 2 ^ 59
def prefixEnd_74836 : Nat := 4983230072969 + 3 ^ 40 * 74836 * 2
def baseEnd_74836 : Nat := 22771459709614481484943

theorem tailTrace_74836 : CollatzResearch.WordTrace tailWord_74836 prefixEnd_74836 22771459709614481484943 := by
  unfold tailWord_74836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364746578444713908182181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1819662104592951877576241 1364746578444713908182181)
  ·
    refine ⟨255889983458383857784159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1364746578444713908182181 255889983458383857784159)
    ·
      refine ⟨383834975187575786676239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255889983458383857784159 383834975187575786676239)
      ·
        refine ⟨575752462781363680014359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383834975187575786676239 575752462781363680014359)
        ·
          refine ⟨863628694172045520021539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575752462781363680014359 863628694172045520021539)
          ·
            refine ⟨1295443041258068280032309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863628694172045520021539 1295443041258068280032309)
            ·
              refine ⟨121447785117943901253029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1295443041258068280032309 121447785117943901253029)
              ·
                refine ⟨22771459709614481484943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121447785117943901253029 22771459709614481484943)
                ·
                  rfl

theorem cell19_74836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_74836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74836 prefixEnd_74836 := by exact prefixLift 74836
  have htrace : WordTrace (prefixWord ++ tailWord_74836) baseStart_74836 baseEnd_74836 := by
    simpa [prefixWord, tailWord_74836, baseEnd_74836] using wordTrace_append hprefix tailTrace_74836
  have hstable : (prefixWord ++ tailWord_74836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74836).length < 2 ^ (prefixWord ++ tailWord_74836).sum := by decide
  have hdescent : baseEnd_74836 < baseStart_74836 := by decide
  rcases family_descends (prefixWord ++ tailWord_74836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74876 : List Nat := [2, 2, 2, 1, 1, 3, 8]
def baseStart_74876 : Nat := 118140960795 + 74876 * 2 ^ 59
def prefixEnd_74876 : Nat := 4983230072969 + 3 ^ 40 * 74876 * 2
def baseEnd_74876 : Nat := 7594543700968746865315

theorem tailTrace_74876 : CollatzResearch.WordTrace tailWord_74876 prefixEnd_74876 7594543700968746865315 := by
  unfold tailWord_74876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365476038372257323910241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1820634717829676431880321 1365476038372257323910241)
  ·
    refine ⟨1024107028779192992932681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1365476038372257323910241 1024107028779192992932681)
    ·
      refine ⟨768080271584394744699511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1024107028779192992932681 768080271584394744699511)
      ·
        refine ⟨1152120407376592117049267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768080271584394744699511 1152120407376592117049267)
        ·
          refine ⟨1728180611064888175573901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152120407376592117049267 1728180611064888175573901)
          ·
            refine ⟨648067729149333065840213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1728180611064888175573901 648067729149333065840213)
            ·
              refine ⟨7594543700968746865315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 648067729149333065840213 7594543700968746865315)
              ·
                rfl

theorem cell19_74876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_74876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74876 prefixEnd_74876 := by exact prefixLift 74876
  have htrace : WordTrace (prefixWord ++ tailWord_74876) baseStart_74876 baseEnd_74876 := by
    simpa [prefixWord, tailWord_74876, baseEnd_74876] using wordTrace_append hprefix tailTrace_74876
  have hstable : (prefixWord ++ tailWord_74876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74876).length < 2 ^ (prefixWord ++ tailWord_74876).sum := by decide
  have hdescent : baseEnd_74876 < baseStart_74876 := by decide
  rcases family_descends (prefixWord ++ tailWord_74876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74910 : List Nat := [4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_74910 : Nat := 118140960795 + 74910 * 2 ^ 59
def prefixEnd_74910 : Nat := 4983230072969 + 3 ^ 40 * 74910 * 2
def baseEnd_74910 : Nat := 22793976787204235840297

theorem tailTrace_74910 : CollatzResearch.WordTrace tailWord_74910 prefixEnd_74910 22793976787204235840297 := by
  unfold tailWord_74910
  simp only [CollatzResearch.WordTrace]
  refine ⟨341524019827667306819773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1821461439080892303038789 341524019827667306819773)
  ·
    refine ⟨128071507435375240057415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 341524019827667306819773 128071507435375240057415)
    ·
      refine ⟨192107261153062860086123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128071507435375240057415 192107261153062860086123)
      ·
        refine ⟨288160891729594290129185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192107261153062860086123 288160891729594290129185)
        ·
          refine ⟨216120668797195717596889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288160891729594290129185 216120668797195717596889)
          ·
            refine ⟨162090501597896788197667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216120668797195717596889 162090501597896788197667)
            ·
              refine ⟨243135752396845182296501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162090501597896788197667 243135752396845182296501)
              ·
                refine ⟨22793976787204235840297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 243135752396845182296501 22793976787204235840297)
                ·
                  rfl

theorem cell19_74910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_74910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74910 prefixEnd_74910 := by exact prefixLift 74910
  have htrace : WordTrace (prefixWord ++ tailWord_74910) baseStart_74910 baseEnd_74910 := by
    simpa [prefixWord, tailWord_74910, baseEnd_74910] using wordTrace_append hprefix tailTrace_74910
  have hstable : (prefixWord ++ tailWord_74910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74910).length < 2 ^ (prefixWord ++ tailWord_74910).sum := by decide
  have hdescent : baseEnd_74910 < baseStart_74910 := by decide
  rcases family_descends (prefixWord ++ tailWord_74910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74948 : List Nat := [2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_74948 : Nat := 118140960795 + 74948 * 2 ^ 59
def prefixEnd_74948 : Nat := 4983230072969 + 3 ^ 40 * 74948 * 2
def baseEnd_74948 : Nat := 22805539610831406995749

theorem tailTrace_74948 : CollatzResearch.WordTrace tailWord_74948 prefixEnd_74948 22805539610831406995749 := by
  unfold tailWord_74948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366789066241835472220749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1822385421655780629627665 1366789066241835472220749)
  ·
    refine ⟨512545899840688302082781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1366789066241835472220749 512545899840688302082781)
    ·
      refine ⟨192204712440258113281043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 512545899840688302082781 192204712440258113281043)
      ·
        refine ⟨288307068660387169921565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192204712440258113281043 288307068660387169921565)
        ·
          refine ⟨108115150747645188720587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288307068660387169921565 108115150747645188720587)
          ·
            refine ⟨162172726121467783080881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108115150747645188720587 162172726121467783080881)
            ·
              refine ⟨121629544591100837310661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162172726121467783080881 121629544591100837310661)
              ·
                refine ⟨22805539610831406995749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121629544591100837310661 22805539610831406995749)
                ·
                  rfl

theorem cell19_74948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_74948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74948 prefixEnd_74948 := by exact prefixLift 74948
  have htrace : WordTrace (prefixWord ++ tailWord_74948) baseStart_74948 baseEnd_74948 := by
    simpa [prefixWord, tailWord_74948, baseEnd_74948] using wordTrace_append hprefix tailTrace_74948
  have hstable : (prefixWord ++ tailWord_74948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74948).length < 2 ^ (prefixWord ++ tailWord_74948).sum := by decide
  have hdescent : baseEnd_74948 < baseStart_74948 := by decide
  rcases family_descends (prefixWord ++ tailWord_74948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74952 : List Nat := [2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_74952 : Nat := 118140960795 + 74952 * 2 ^ 59
def prefixEnd_74952 : Nat := 4983230072969 + 3 ^ 40 * 74952 * 2
def baseEnd_74952 : Nat := 22806756750160582906849

theorem tailTrace_74952 : CollatzResearch.WordTrace tailWord_74952 prefixEnd_74952 22806756750160582906849 := by
  unfold tailWord_74952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366862012234589813793555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1822482682979453085058073 1366862012234589813793555)
  ·
    refine ⟨2050293018351884720690333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1366862012234589813793555 2050293018351884720690333)
    ·
      refine ⟨768859881881956770258875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2050293018351884720690333 768859881881956770258875)
      ·
        refine ⟨1153289822822935155388313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768859881881956770258875 1153289822822935155388313)
        ·
          refine ⟨864967367117201366541235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153289822822935155388313 864967367117201366541235)
          ·
            refine ⟨1297451050675802049811853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864967367117201366541235 1297451050675802049811853)
            ·
              refine ⟨486544144003425768679445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1297451050675802049811853 486544144003425768679445)
              ·
                refine ⟨22806756750160582906849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 486544144003425768679445 22806756750160582906849)
                ·
                  rfl

theorem cell19_74952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_74952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_74952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_74952 prefixEnd_74952 := by exact prefixLift 74952
  have htrace : WordTrace (prefixWord ++ tailWord_74952) baseStart_74952 baseEnd_74952 := by
    simpa [prefixWord, tailWord_74952, baseEnd_74952] using wordTrace_append hprefix tailTrace_74952
  have hstable : (prefixWord ++ tailWord_74952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74952).length < 2 ^ (prefixWord ++ tailWord_74952).sum := by decide
  have hdescent : baseEnd_74952 < baseStart_74952 := by decide
  rcases family_descends (prefixWord ++ tailWord_74952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75007 : List Nat := [1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_75007 : Nat := 118140960795 + 75007 * 2 ^ 59
def prefixEnd_75007 : Nat := 4983230072969 + 3 ^ 40 * 75007 * 2
def baseEnd_75007 : Nat := 22823492415936751684477

theorem tailTrace_75007 : CollatzResearch.WordTrace tailWord_75007 prefixEnd_75007 22823492415936751684477 := by
  unfold tailWord_75007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735730039269924020839275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1823820026179949347226183 2735730039269924020839275)
  ·
    refine ⟨4103595058904886031258913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2735730039269924020839275 4103595058904886031258913)
    ·
      refine ⟨3077696294178664523444185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4103595058904886031258913 3077696294178664523444185)
      ·
        refine ⟨2308272220633998392583139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3077696294178664523444185 2308272220633998392583139)
        ·
          refine ⟨3462408330950997588874709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308272220633998392583139 3462408330950997588874709)
          ·
            refine ⟨81150195256664005989251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3462408330950997588874709 81150195256664005989251)
            ·
              refine ⟨121725292884996008983877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81150195256664005989251 121725292884996008983877)
              ·
                refine ⟨22823492415936751684477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121725292884996008983877 22823492415936751684477)
                ·
                  rfl

theorem cell19_75007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_75007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75007 prefixEnd_75007 := by exact prefixLift 75007
  have htrace : WordTrace (prefixWord ++ tailWord_75007) baseStart_75007 baseEnd_75007 := by
    simpa [prefixWord, tailWord_75007, baseEnd_75007] using wordTrace_append hprefix tailTrace_75007
  have hstable : (prefixWord ++ tailWord_75007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75007).length < 2 ^ (prefixWord ++ tailWord_75007).sum := by decide
  have hdescent : baseEnd_75007 < baseStart_75007 := by decide
  rcases family_descends (prefixWord ++ tailWord_75007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75066 : List Nat := [3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_75066 : Nat := 118140960795 + 75066 * 2 ^ 59
def prefixEnd_75066 : Nat := 4983230072969 + 3 ^ 40 * 75066 * 2
def baseEnd_75066 : Nat := 22841445221042096373205

theorem tailTrace_75066 : CollatzResearch.WordTrace tailWord_75066 prefixEnd_75066 22841445221042096373205 := by
  unfold tailWord_75066
  simp only [CollatzResearch.WordTrace]
  refine ⟨684470486514044274309263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1825254630704118064824701 684470486514044274309263)
  ·
    refine ⟨1026705729771066411463895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 684470486514044274309263 1026705729771066411463895)
    ·
      refine ⟨1540058594656599617195843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026705729771066411463895 1540058594656599617195843)
      ·
        refine ⟨2310087891984899425793765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540058594656599617195843 2310087891984899425793765)
        ·
          refine ⟨433141479747168642336331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2310087891984899425793765 433141479747168642336331)
          ·
            refine ⟨649712219620752963504497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433141479747168642336331 649712219620752963504497)
            ·
              refine ⟨487284164715564722628373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649712219620752963504497 487284164715564722628373)
              ·
                refine ⟨22841445221042096373205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 487284164715564722628373 22841445221042096373205)
                ·
                  rfl

theorem cell19_75066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_75066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75066 prefixEnd_75066 := by exact prefixLift 75066
  have htrace : WordTrace (prefixWord ++ tailWord_75066) baseStart_75066 baseEnd_75066 := by
    simpa [prefixWord, tailWord_75066, baseEnd_75066] using wordTrace_append hprefix tailTrace_75066
  have hstable : (prefixWord ++ tailWord_75066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75066).length < 2 ^ (prefixWord ++ tailWord_75066).sum := by decide
  have hdescent : baseEnd_75066 < baseStart_75066 := by decide
  rcases family_descends (prefixWord ++ tailWord_75066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75094 : List Nat := [5, 2, 3, 1, 2, 1, 5]
def baseStart_75094 : Nat := 118140960795 + 75094 * 2 ^ 59
def prefixEnd_75094 : Nat := 4983230072969 + 3 ^ 40 * 75094 * 2
def baseEnd_75094 : Nat := 7616655065448775916969

theorem tailTrace_75094 : CollatzResearch.WordTrace tailWord_75094 prefixEnd_75094 7616655065448775916969 := by
  unfold tailWord_75094
  simp only [CollatzResearch.WordTrace]
  refine ⟨171181449372171117453521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1825935459969825252837557 171181449372171117453521)
  ·
    refine ⟨128386087029128338090141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171181449372171117453521 128386087029128338090141)
    ·
      refine ⟨48144782635923126783803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128386087029128338090141 48144782635923126783803)
      ·
        refine ⟨72217173953884690175705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48144782635923126783803 72217173953884690175705)
        ·
          refine ⟨54162880465413517631779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72217173953884690175705 54162880465413517631779)
          ·
            refine ⟨81244320698120276447669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54162880465413517631779 81244320698120276447669)
            ·
              refine ⟨7616655065448775916969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81244320698120276447669 7616655065448775916969)
              ·
                rfl

theorem cell19_75094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_75094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75094 prefixEnd_75094 := by exact prefixLift 75094
  have htrace : WordTrace (prefixWord ++ tailWord_75094) baseStart_75094 baseEnd_75094 := by
    simpa [prefixWord, tailWord_75094, baseEnd_75094] using wordTrace_append hprefix tailTrace_75094
  have hstable : (prefixWord ++ tailWord_75094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75094).length < 2 ^ (prefixWord ++ tailWord_75094).sum := by decide
  have hdescent : baseEnd_75094 < baseStart_75094 := by decide
  rcases family_descends (prefixWord ++ tailWord_75094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75104 : List Nat := [2, 1, 1, 3, 4, 1, 7]
def baseStart_75104 : Nat := 118140960795 + 75104 * 2 ^ 59
def prefixEnd_75104 : Nat := 4983230072969 + 3 ^ 40 * 75104 * 2
def baseEnd_75104 : Nat := 7617669348223089176219

theorem tailTrace_75104 : CollatzResearch.WordTrace tailWord_75104 prefixEnd_75104 7617669348223089176219 := by
  unfold tailWord_75104
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369633959959254793560183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1826178613279006391413577 1369633959959254793560183)
  ·
    refine ⟨2054450939938882190340275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1369633959959254793560183 2054450939938882190340275)
    ·
      refine ⟨3081676409908323285510413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2054450939938882190340275 3081676409908323285510413)
      ·
        refine ⟨1155628653715621232066405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3081676409908323285510413 1155628653715621232066405)
        ·
          refine ⟨216680372571678981012451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1155628653715621232066405 216680372571678981012451)
          ·
            refine ⟨325020558857518471518677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216680372571678981012451 325020558857518471518677)
            ·
              refine ⟨7617669348223089176219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 325020558857518471518677 7617669348223089176219)
              ·
                rfl

theorem cell19_75104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_75104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75104 prefixEnd_75104 := by exact prefixLift 75104
  have htrace : WordTrace (prefixWord ++ tailWord_75104) baseStart_75104 baseEnd_75104 := by
    simpa [prefixWord, tailWord_75104, baseEnd_75104] using wordTrace_append hprefix tailTrace_75104
  have hstable : (prefixWord ++ tailWord_75104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75104).length < 2 ^ (prefixWord ++ tailWord_75104).sum := by decide
  have hdescent : baseEnd_75104 < baseStart_75104 := by decide
  rcases family_descends (prefixWord ++ tailWord_75104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75138 : List Nat := [3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_75138 : Nat := 118140960795 + 75138 * 2 ^ 59
def prefixEnd_75138 : Nat := 4983230072969 + 3 ^ 40 * 75138 * 2
def baseEnd_75138 : Nat := 22863353728967262773009

theorem tailTrace_75138 : CollatzResearch.WordTrace tailWord_75138 prefixEnd_75138 22863353728967262773009 := by
  unfold tailWord_75138
  simp only [CollatzResearch.WordTrace]
  refine ⟨685127000448833348464517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1827005334530222262572045 685127000448833348464517)
  ·
    refine ⟨128461312584156252837097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 685127000448833348464517 128461312584156252837097)
    ·
      refine ⟨96345984438117189627823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128461312584156252837097 96345984438117189627823)
      ·
        refine ⟨144518976657175784441735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96345984438117189627823 144518976657175784441735)
        ·
          refine ⟨216778464985763676662603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144518976657175784441735 216778464985763676662603)
          ·
            refine ⟨325167697478645514993905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216778464985763676662603 325167697478645514993905)
            ·
              refine ⟨243875773108984136245429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325167697478645514993905 243875773108984136245429)
              ·
                refine ⟨22863353728967262773009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 243875773108984136245429 22863353728967262773009)
                ·
                  rfl

theorem cell19_75138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_75138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75138 prefixEnd_75138 := by exact prefixLift 75138
  have htrace : WordTrace (prefixWord ++ tailWord_75138) baseStart_75138 baseEnd_75138 := by
    simpa [prefixWord, tailWord_75138, baseEnd_75138] using wordTrace_append hprefix tailTrace_75138
  have hstable : (prefixWord ++ tailWord_75138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75138).length < 2 ^ (prefixWord ++ tailWord_75138).sum := by decide
  have hdescent : baseEnd_75138 < baseStart_75138 := by decide
  rcases family_descends (prefixWord ++ tailWord_75138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75180 : List Nat := [2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_75180 : Nat := 118140960795 + 75180 * 2 ^ 59
def prefixEnd_75180 : Nat := 4983230072969 + 3 ^ 40 * 75180 * 2
def baseEnd_75180 : Nat := 22876133691923609839561

theorem tailTrace_75180 : CollatzResearch.WordTrace tailWord_75180 prefixEnd_75180 22876133691923609839561 := by
  unfold tailWord_75180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371019933821587283443497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1828026578428783044591329 1371019933821587283443497)
  ·
    refine ⟨1028264950366190462582623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1371019933821587283443497 1028264950366190462582623)
    ·
      refine ⟨1542397425549285693873935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028264950366190462582623 1542397425549285693873935)
      ·
        refine ⟨2313596138323928540810903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542397425549285693873935 2313596138323928540810903)
        ·
          refine ⟨3470394207485892811216355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313596138323928540810903 3470394207485892811216355)
          ·
            refine ⟨5205591311228839216824533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470394207485892811216355 5205591311228839216824533)
            ·
              refine ⟨122006046356925919144325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5205591311228839216824533 122006046356925919144325)
              ·
                refine ⟨22876133691923609839561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122006046356925919144325 22876133691923609839561)
                ·
                  rfl

theorem cell19_75180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_75180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75180 prefixEnd_75180 := by exact prefixLift 75180
  have htrace : WordTrace (prefixWord ++ tailWord_75180) baseStart_75180 baseEnd_75180 := by
    simpa [prefixWord, tailWord_75180, baseEnd_75180] using wordTrace_append hprefix tailTrace_75180
  have hstable : (prefixWord ++ tailWord_75180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75180).length < 2 ^ (prefixWord ++ tailWord_75180).sum := by decide
  have hdescent : baseEnd_75180 < baseStart_75180 := by decide
  rcases family_descends (prefixWord ++ tailWord_75180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75197 : List Nat := [1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_75197 : Nat := 118140960795 + 75197 * 2 ^ 59
def prefixEnd_75197 : Nat := 4983230072969 + 3 ^ 40 * 75197 * 2
def baseEnd_75197 : Nat := 22881306534072607461737

theorem tailTrace_75197 : CollatzResearch.WordTrace tailWord_75197 prefixEnd_75197 22881306534072607461737 := by
  unfold tailWord_75197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742659908581586470255845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1828439939054390980170563 2742659908581586470255845)
  ·
    refine ⟨514248732859047463172971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2742659908581586470255845 514248732859047463172971)
    ·
      refine ⟨771373099288571194759457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514248732859047463172971 771373099288571194759457)
      ·
        refine ⟨578529824466428396069593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771373099288571194759457 578529824466428396069593)
        ·
          refine ⟨433897368349821297052195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578529824466428396069593 433897368349821297052195)
          ·
            refine ⟨650846052524731945578293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433897368349821297052195 650846052524731945578293)
            ·
              refine ⟨61016817424193619897965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 650846052524731945578293 61016817424193619897965)
              ·
                refine ⟨22881306534072607461737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61016817424193619897965 22881306534072607461737)
                ·
                  rfl

theorem cell19_75197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_75197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75197 prefixEnd_75197 := by exact prefixLift 75197
  have htrace : WordTrace (prefixWord ++ tailWord_75197) baseStart_75197 baseEnd_75197 := by
    simpa [prefixWord, tailWord_75197, baseEnd_75197] using wordTrace_append hprefix tailTrace_75197
  have hstable : (prefixWord ++ tailWord_75197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75197).length < 2 ^ (prefixWord ++ tailWord_75197).sum := by decide
  have hdescent : baseEnd_75197 < baseStart_75197 := by decide
  rcases family_descends (prefixWord ++ tailWord_75197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75254 : List Nat := [5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_75254 : Nat := 118140960795 + 75254 * 2 ^ 59
def prefixEnd_75254 : Nat := 4983230072969 + 3 ^ 40 * 75254 * 2
def baseEnd_75254 : Nat := 22898650769513364194915

theorem tailTrace_75254 : CollatzResearch.WordTrace tailWord_75254 prefixEnd_75254 22898650769513364194915 := by
  unfold tailWord_75254
  simp only [CollatzResearch.WordTrace]
  refine ⟨171546179335942825317551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1829825912916723470053877 171546179335942825317551)
  ·
    refine ⟨257319269003914237976327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171546179335942825317551 257319269003914237976327)
    ·
      refine ⟨385978903505871356964491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257319269003914237976327 385978903505871356964491)
      ·
        refine ⟨578968355258807035446737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385978903505871356964491 578968355258807035446737)
        ·
          refine ⟨434226266444105276585053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578968355258807035446737 434226266444105276585053)
          ·
            refine ⟨162834849916539478719395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434226266444105276585053 162834849916539478719395)
            ·
              refine ⟨244252274874809218079093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162834849916539478719395 244252274874809218079093)
              ·
                refine ⟨22898650769513364194915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244252274874809218079093 22898650769513364194915)
                ·
                  rfl

theorem cell19_75254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_75254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75254 prefixEnd_75254 := by exact prefixLift 75254
  have htrace : WordTrace (prefixWord ++ tailWord_75254) baseStart_75254 baseEnd_75254 := by
    simpa [prefixWord, tailWord_75254, baseEnd_75254] using wordTrace_append hprefix tailTrace_75254
  have hstable : (prefixWord ++ tailWord_75254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75254).length < 2 ^ (prefixWord ++ tailWord_75254).sum := by decide
  have hdescent : baseEnd_75254 < baseStart_75254 := by decide
  rcases family_descends (prefixWord ++ tailWord_75254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75256 : List Nat := [2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_75256 : Nat := 118140960795 + 75256 * 2 ^ 59
def prefixEnd_75256 : Nat := 4983230072969 + 3 ^ 40 * 75256 * 2
def baseEnd_75256 : Nat := 22899259339177952150465

theorem tailTrace_75256 : CollatzResearch.WordTrace tailWord_75256 prefixEnd_75256 22899259339177952150465 := by
  unfold tailWord_75256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372405907683919773326811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1829874543578559697769081 1372405907683919773326811)
  ·
    refine ⟨2058608861525879659990217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1372405907683919773326811 2058608861525879659990217)
    ·
      refine ⟨1543956646144409744992663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2058608861525879659990217 1543956646144409744992663)
      ·
        refine ⟨2315934969216614617488995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543956646144409744992663 2315934969216614617488995)
        ·
          refine ⟨3473902453824921926233493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315934969216614617488995 3473902453824921926233493)
          ·
            refine ⟨162839177523043215292195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3473902453824921926233493 162839177523043215292195)
            ·
              refine ⟨244258766284564822938293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162839177523043215292195 244258766284564822938293)
              ·
                refine ⟨22899259339177952150465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244258766284564822938293 22899259339177952150465)
                ·
                  rfl

theorem cell19_75256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_75256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75256 prefixEnd_75256 := by exact prefixLift 75256
  have htrace : WordTrace (prefixWord ++ tailWord_75256) baseStart_75256 baseEnd_75256 := by
    simpa [prefixWord, tailWord_75256, baseEnd_75256] using wordTrace_append hprefix tailTrace_75256
  have hstable : (prefixWord ++ tailWord_75256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75256).length < 2 ^ (prefixWord ++ tailWord_75256).sum := by decide
  have hdescent : baseEnd_75256 < baseStart_75256 := by decide
  rcases family_descends (prefixWord ++ tailWord_75256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75351 : List Nat := [1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_75351 : Nat := 118140960795 + 75351 * 2 ^ 59
def prefixEnd_75351 : Nat := 4983230072969 + 3 ^ 40 * 75351 * 2
def baseEnd_75351 : Nat := 22928166398245880039095

theorem tailTrace_75351 : CollatzResearch.WordTrace tailWord_75351 prefixEnd_75351 22928166398245880039095 := by
  unfold tailWord_75351
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748276750023670771361907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1832184500015780514241271 2748276750023670771361907)
  ·
    refine ⟨4122415125035506157042861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748276750023670771361907 4122415125035506157042861)
    ·
      refine ⟨1545905671888314808891073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4122415125035506157042861 1545905671888314808891073)
      ·
        refine ⟨1159429253916236106668305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545905671888314808891073 1159429253916236106668305)
        ·
          refine ⟨869571940437177080001229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159429253916236106668305 869571940437177080001229)
          ·
            refine ⟨326089477663941405000461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 869571940437177080001229 326089477663941405000461)
            ·
              refine ⟨122283554123978026875173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326089477663941405000461 122283554123978026875173)
              ·
                refine ⟨22928166398245880039095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122283554123978026875173 22928166398245880039095)
                ·
                  rfl

theorem cell19_75351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_75351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75351 prefixEnd_75351 := by exact prefixLift 75351
  have htrace : WordTrace (prefixWord ++ tailWord_75351) baseStart_75351 baseEnd_75351 := by
    simpa [prefixWord, tailWord_75351, baseEnd_75351] using wordTrace_append hprefix tailTrace_75351
  have hstable : (prefixWord ++ tailWord_75351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75351).length < 2 ^ (prefixWord ++ tailWord_75351).sum := by decide
  have hdescent : baseEnd_75351 < baseStart_75351 := by decide
  rcases family_descends (prefixWord ++ tailWord_75351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75389 : List Nat := [1, 4, 1, 1, 4, 2, 6]
def baseStart_75389 : Nat := 118140960795 + 75389 * 2 ^ 59
def prefixEnd_75389 : Nat := 4983230072969 + 3 ^ 40 * 75389 * 2
def baseEnd_75389 : Nat := 7646576407291017064849

theorem tailTrace_75389 : CollatzResearch.WordTrace tailWord_75389 prefixEnd_75389 7646576407291017064849 := by
  unfold tailWord_75389
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749662723886003261245221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1833108482590668840830147 2749662723886003261245221)
  ·
    refine ⟨515561760728625611483479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2749662723886003261245221 515561760728625611483479)
    ·
      refine ⟨773342641092938417225219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515561760728625611483479 773342641092938417225219)
      ·
        refine ⟨1160013961639407625837829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773342641092938417225219 1160013961639407625837829)
        ·
          refine ⟨217502617807388929844593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1160013961639407625837829 217502617807388929844593)
          ·
            refine ⟨163126963355541697383445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217502617807388929844593 163126963355541697383445)
            ·
              refine ⟨7646576407291017064849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163126963355541697383445 7646576407291017064849)
              ·
                rfl

theorem cell19_75389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_75389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75389 prefixEnd_75389 := by exact prefixLift 75389
  have htrace : WordTrace (prefixWord ++ tailWord_75389) baseStart_75389 baseEnd_75389 := by
    simpa [prefixWord, tailWord_75389, baseEnd_75389] using wordTrace_append hprefix tailTrace_75389
  have hstable : (prefixWord ++ tailWord_75389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75389).length < 2 ^ (prefixWord ++ tailWord_75389).sum := by decide
  have hdescent : baseEnd_75389 < baseStart_75389 := by decide
  rcases family_descends (prefixWord ++ tailWord_75389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75425 : List Nat := [1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_75425 : Nat := 118140960795 + 75425 * 2 ^ 59
def prefixEnd_75425 : Nat := 4983230072969 + 3 ^ 40 * 75425 * 2
def baseEnd_75425 : Nat := 22950683475835634394449

theorem tailTrace_75425 : CollatzResearch.WordTrace tailWord_75425 prefixEnd_75425 22950683475835634394449 := by
  unfold tailWord_75425
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750975751755581409555729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1833983834503720939703819 2750975751755581409555729)
  ·
    refine ⟨2063231813816686057166797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2750975751755581409555729 2063231813816686057166797)
    ·
      refine ⟨773711930181257271437549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2063231813816686057166797 773711930181257271437549)
      ·
        refine ⟨290141973817971476789081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 773711930181257271437549 290141973817971476789081)
        ·
          refine ⟨217606480363478607591811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290141973817971476789081 217606480363478607591811)
          ·
            refine ⟨326409720545217911387717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217606480363478607591811 326409720545217911387717)
            ·
              refine ⟨61201822602228358385197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 326409720545217911387717 61201822602228358385197)
              ·
                refine ⟨22950683475835634394449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61201822602228358385197 22950683475835634394449)
                ·
                  rfl

theorem cell19_75425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_75425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75425 prefixEnd_75425 := by exact prefixLift 75425
  have htrace : WordTrace (prefixWord ++ tailWord_75425) baseStart_75425 baseEnd_75425 := by
    simpa [prefixWord, tailWord_75425, baseEnd_75425] using wordTrace_append hprefix tailTrace_75425
  have hstable : (prefixWord ++ tailWord_75425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75425).length < 2 ^ (prefixWord ++ tailWord_75425).sum := by decide
  have hdescent : baseEnd_75425 < baseStart_75425 := by decide
  rcases family_descends (prefixWord ++ tailWord_75425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75505 : List Nat := [1, 2, 2, 2, 2, 10]
def baseStart_75505 : Nat := 118140960795 + 75505 * 2 ^ 59
def prefixEnd_75505 : Nat := 4983230072969 + 3 ^ 40 * 75505 * 2
def baseEnd_75505 : Nat := 2552780695824350290717

theorem tailTrace_75505 : CollatzResearch.WordTrace tailWord_75505 prefixEnd_75505 2552780695824350290717 := by
  unfold tailWord_75505
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753893591465755072467969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1835929060977170048311979 2753893591465755072467969)
  ·
    refine ⟨2065420193599316304350977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2753893591465755072467969 2065420193599316304350977)
    ·
      refine ⟨1549065145199487228263233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2065420193599316304350977 1549065145199487228263233)
      ·
        refine ⟨1161798858899615421197425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1549065145199487228263233 1161798858899615421197425)
        ·
          refine ⟨871349144174711565898069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161798858899615421197425 871349144174711565898069)
          ·
            refine ⟨2552780695824350290717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 871349144174711565898069 2552780695824350290717)
            ·
              rfl

theorem cell19_75505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_75505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75505 prefixEnd_75505 := by exact prefixLift 75505
  have htrace : WordTrace (prefixWord ++ tailWord_75505) baseStart_75505 baseEnd_75505 := by
    simpa [prefixWord, tailWord_75505, baseEnd_75505] using wordTrace_append hprefix tailTrace_75505
  have hstable : (prefixWord ++ tailWord_75505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75505).length < 2 ^ (prefixWord ++ tailWord_75505).sum := by decide
  have hdescent : baseEnd_75505 < baseStart_75505 := by decide
  rcases family_descends (prefixWord ++ tailWord_75505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75518 : List Nat := [4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_75518 : Nat := 118140960795 + 75518 * 2 ^ 59
def prefixEnd_75518 : Nat := 4983230072969 + 3 ^ 40 * 75518 * 2
def baseEnd_75518 : Nat := 22978981965238974327529

theorem tailTrace_75518 : CollatzResearch.WordTrace tailWord_75518 prefixEnd_75518 22978981965238974327529 := by
  unfold tailWord_75518
  simp only [CollatzResearch.WordTrace]
  refine ⟨344295967552332286586401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1836245160279105528460805 344295967552332286586401)
  ·
    refine ⟨258221975664249214939801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 344295967552332286586401 258221975664249214939801)
    ·
      refine ⟨193666481748186911204851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258221975664249214939801 193666481748186911204851)
      ·
        refine ⟨290499722622280366807277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193666481748186911204851 290499722622280366807277)
        ·
          refine ⟨108937395983355137552729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290499722622280366807277 108937395983355137552729)
          ·
            refine ⟨81703046987516353164547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108937395983355137552729 81703046987516353164547)
            ·
              refine ⟨122554570481274529746821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81703046987516353164547 122554570481274529746821)
              ·
                refine ⟨22978981965238974327529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122554570481274529746821 22978981965238974327529)
                ·
                  rfl

theorem cell19_75518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_75518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75518 prefixEnd_75518 := by exact prefixLift 75518
  have htrace : WordTrace (prefixWord ++ tailWord_75518) baseStart_75518 baseEnd_75518 := by
    simpa [prefixWord, tailWord_75518, baseEnd_75518] using wordTrace_append hprefix tailTrace_75518
  have hstable : (prefixWord ++ tailWord_75518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75518).length < 2 ^ (prefixWord ++ tailWord_75518).sum := by decide
  have hdescent : baseEnd_75518 < baseStart_75518 := by decide
  rcases family_descends (prefixWord ++ tailWord_75518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75560 : List Nat := [2, 1, 5, 1, 1, 3, 6]
def baseStart_75560 : Nat := 118140960795 + 75560 * 2 ^ 59
def prefixEnd_75560 : Nat := 4983230072969 + 3 ^ 40 * 75560 * 2
def baseEnd_75560 : Nat := 7663920642731773798027

theorem tailTrace_75560 : CollatzResearch.WordTrace tailWord_75560 prefixEnd_75560 7663920642731773798027 := by
  unfold tailWord_75560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377949803133249732860067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1837266404177666310480089 1377949803133249732860067)
  ·
    refine ⟨2066924704699874599290101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1377949803133249732860067 2066924704699874599290101)
    ·
      refine ⟨193774191065613243683447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2066924704699874599290101 193774191065613243683447)
      ·
        refine ⟨290661286598419865525171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193774191065613243683447 290661286598419865525171)
        ·
          refine ⟨435991929897629798287757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290661286598419865525171 435991929897629798287757)
          ·
            refine ⟨163496973711611174357909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 435991929897629798287757 163496973711611174357909)
            ·
              refine ⟨7663920642731773798027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163496973711611174357909 7663920642731773798027)
              ·
                rfl

theorem cell19_75560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_75560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75560 prefixEnd_75560 := by exact prefixLift 75560
  have htrace : WordTrace (prefixWord ++ tailWord_75560) baseStart_75560 baseEnd_75560 := by
    simpa [prefixWord, tailWord_75560, baseEnd_75560] using wordTrace_append hprefix tailTrace_75560
  have hstable : (prefixWord ++ tailWord_75560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75560).length < 2 ^ (prefixWord ++ tailWord_75560).sum := by decide
  have hdescent : baseEnd_75560 < baseStart_75560 := by decide
  rcases family_descends (prefixWord ++ tailWord_75560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75657 : List Nat := [1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_75657 : Nat := 118140960795 + 75657 * 2 ^ 59
def prefixEnd_75657 : Nat := 4983230072969 + 3 ^ 40 * 75657 * 2
def baseEnd_75657 : Nat := 23021277556927837238261

theorem tailTrace_75657 : CollatzResearch.WordTrace tailWord_75657 prefixEnd_75657 23021277556927837238261 := by
  unfold tailWord_75657
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759437486915085032001225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1839624991276723354667483 2759437486915085032001225)
  ·
    refine ⟨2069578115186313774000919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2759437486915085032001225 2069578115186313774000919)
    ·
      refine ⟨3104367172779470661001379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069578115186313774000919 3104367172779470661001379)
      ·
        refine ⟨4656550759169205991502069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104367172779470661001379 4656550759169205991502069)
        ·
          refine ⟨436551633672113061703319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4656550759169205991502069 436551633672113061703319)
          ·
            refine ⟨654827450508169592554979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436551633672113061703319 654827450508169592554979)
            ·
              refine ⟨982241175762254388832469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654827450508169592554979 982241175762254388832469)
              ·
                refine ⟨23021277556927837238261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 982241175762254388832469 23021277556927837238261)
                ·
                  rfl

theorem cell19_75657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_75657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75657 prefixEnd_75657 := by exact prefixLift 75657
  have htrace : WordTrace (prefixWord ++ tailWord_75657) baseStart_75657 baseEnd_75657 := by
    simpa [prefixWord, tailWord_75657, baseEnd_75657] using wordTrace_append hprefix tailTrace_75657
  have hstable : (prefixWord ++ tailWord_75657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75657).length < 2 ^ (prefixWord ++ tailWord_75657).sum := by decide
  have hdescent : baseEnd_75657 < baseStart_75657 := by decide
  rcases family_descends (prefixWord ++ tailWord_75657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75670 : List Nat := [5, 3, 1, 1, 2, 7]
def baseStart_75670 : Nat := 118140960795 + 75670 * 2 ^ 59
def prefixEnd_75670 : Nat := 4983230072969 + 3 ^ 40 * 75670 * 2
def baseEnd_75670 : Nat := 2558359251083073216593

theorem tailTrace_75670 : CollatzResearch.WordTrace tailWord_75670 prefixEnd_75670 2558359251083073216593 := by
  unfold tailWord_75670
  simp only [CollatzResearch.WordTrace]
  refine ⟨172494477241749265764029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1839941090578658834816309 172494477241749265764029)
  ·
    refine ⟨64685428965655974661511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172494477241749265764029 64685428965655974661511)
    ·
      refine ⟨97028143448483961992267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64685428965655974661511 97028143448483961992267)
      ·
        refine ⟨145542215172725942988401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97028143448483961992267 145542215172725942988401)
        ·
          refine ⟨109156661379544457241301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145542215172725942988401 109156661379544457241301)
          ·
            refine ⟨2558359251083073216593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 109156661379544457241301 2558359251083073216593)
            ·
              rfl

theorem cell19_75670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_75670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75670 prefixEnd_75670 := by exact prefixLift 75670
  have htrace : WordTrace (prefixWord ++ tailWord_75670) baseStart_75670 baseEnd_75670 := by
    simpa [prefixWord, tailWord_75670, baseEnd_75670] using wordTrace_append hprefix tailTrace_75670
  have hstable : (prefixWord ++ tailWord_75670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75670).length < 2 ^ (prefixWord ++ tailWord_75670).sum := by decide
  have hdescent : baseEnd_75670 < baseStart_75670 := by decide
  rcases family_descends (prefixWord ++ tailWord_75670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75672 : List Nat := [2, 1, 2, 6, 2, 6]
def baseStart_75672 : Nat := 118140960795 + 75672 * 2 ^ 59
def prefixEnd_75672 : Nat := 4983230072969 + 3 ^ 40 * 75672 * 2
def baseEnd_75672 : Nat := 2558426869934694100543

theorem tailTrace_75672 : CollatzResearch.WordTrace tailWord_75672 prefixEnd_75672 2558426869934694100543 := by
  unfold tailWord_75672
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379992290930371296898635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1839989721240495062531513 1379992290930371296898635)
  ·
    refine ⟨2069988436395556945347953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379992290930371296898635 2069988436395556945347953)
    ·
      refine ⟨1552491327296667709010965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2069988436395556945347953 1552491327296667709010965)
      ·
        refine ⟨72773030967031298859889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1552491327296667709010965 72773030967031298859889)
        ·
          refine ⟨54579773225273474144917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72773030967031298859889 54579773225273474144917)
          ·
            refine ⟨2558426869934694100543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54579773225273474144917 2558426869934694100543)
            ·
              rfl

theorem cell19_75672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_75672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75672 prefixEnd_75672 := by exact prefixLift 75672
  have htrace : WordTrace (prefixWord ++ tailWord_75672) baseStart_75672 baseEnd_75672 := by
    simpa [prefixWord, tailWord_75672, baseEnd_75672] using wordTrace_append hprefix tailTrace_75672
  have hstable : (prefixWord ++ tailWord_75672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75672).length < 2 ^ (prefixWord ++ tailWord_75672).sum := by decide
  have hdescent : baseEnd_75672 < baseStart_75672 := by decide
  rcases family_descends (prefixWord ++ tailWord_75672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75708 : List Nat := [2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_75708 : Nat := 118140960795 + 75708 * 2 ^ 59
def prefixEnd_75708 : Nat := 4983230072969 + 3 ^ 40 * 75708 * 2
def baseEnd_75708 : Nat := 23036796083374830104789

theorem tailTrace_75708 : CollatzResearch.WordTrace tailWord_75708 prefixEnd_75708 23036796083374830104789 := by
  unfold tailWord_75708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380648804865160371053889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1840865073153547161405185 1380648804865160371053889)
  ·
    refine ⟨1035486603648870278290417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380648804865160371053889 1035486603648870278290417)
    ·
      refine ⟨776614952736652708717813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035486603648870278290417 776614952736652708717813)
      ·
        refine ⟨72807651819061191442295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 776614952736652708717813 72807651819061191442295)
        ·
          refine ⟨109211477728591787163443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72807651819061191442295 109211477728591787163443)
          ·
            refine ⟨163817216592887680745165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109211477728591787163443 163817216592887680745165)
            ·
              refine ⟨61431456222332880279437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163817216592887680745165 61431456222332880279437)
              ·
                refine ⟨23036796083374830104789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61431456222332880279437 23036796083374830104789)
                ·
                  rfl

theorem cell19_75708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_75708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75708 prefixEnd_75708 := by exact prefixLift 75708
  have htrace : WordTrace (prefixWord ++ tailWord_75708) baseStart_75708 baseEnd_75708 := by
    simpa [prefixWord, tailWord_75708, baseEnd_75708] using wordTrace_append hprefix tailTrace_75708
  have hstable : (prefixWord ++ tailWord_75708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75708).length < 2 ^ (prefixWord ++ tailWord_75708).sum := by decide
  have hdescent : baseEnd_75708 < baseStart_75708 := by decide
  rcases family_descends (prefixWord ++ tailWord_75708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75710 : List Nat := [4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_75710 : Nat := 118140960795 + 75710 * 2 ^ 59
def prefixEnd_75710 : Nat := 4983230072969 + 3 ^ 40 * 75710 * 2
def baseEnd_75710 : Nat := 23037404653039418060339

theorem tailTrace_75710 : CollatzResearch.WordTrace tailWord_75710 prefixEnd_75710 23037404653039418060339 := by
  unfold tailWord_75710
  simp only [CollatzResearch.WordTrace]
  refine ⟨345171319465384385460073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1840913703815383389120389 345171319465384385460073)
  ·
    refine ⟨258878489599038289095055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 345171319465384385460073 258878489599038289095055)
    ·
      refine ⟨388317734398557433642583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258878489599038289095055 388317734398557433642583)
      ·
        refine ⟨582476601597836150463875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388317734398557433642583 582476601597836150463875)
        ·
          refine ⟨873714902396754225695813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582476601597836150463875 873714902396754225695813)
          ·
            refine ⟨163821544199391417317965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 873714902396754225695813 163821544199391417317965)
            ·
              refine ⟨61433079074771781494237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163821544199391417317965 61433079074771781494237)
              ·
                refine ⟨23037404653039418060339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61433079074771781494237 23037404653039418060339)
                ·
                  rfl

theorem cell19_75710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_75710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75710 prefixEnd_75710 := by exact prefixLift 75710
  have htrace : WordTrace (prefixWord ++ tailWord_75710) baseStart_75710 baseEnd_75710 := by
    simpa [prefixWord, tailWord_75710, baseEnd_75710] using wordTrace_append hprefix tailTrace_75710
  have hstable : (prefixWord ++ tailWord_75710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75710).length < 2 ^ (prefixWord ++ tailWord_75710).sum := by decide
  have hdescent : baseEnd_75710 < baseStart_75710 := by decide
  rcases family_descends (prefixWord ++ tailWord_75710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75712 : List Nat := [2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_75712 : Nat := 118140960795 + 75712 * 2 ^ 59
def prefixEnd_75712 : Nat := 4983230072969 + 3 ^ 40 * 75712 * 2
def baseEnd_75712 : Nat := 23038013222704006015889

theorem tailTrace_75712 : CollatzResearch.WordTrace tailWord_75712 prefixEnd_75712 23038013222704006015889 := by
  unfold tailWord_75712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380721750857914712626695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1840962334477219616835593 1380721750857914712626695)
  ·
    refine ⟨2071082626286872068940043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1380721750857914712626695 2071082626286872068940043)
    ·
      refine ⟨3106623939430308103410065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071082626286872068940043 3106623939430308103410065)
      ·
        refine ⟨2329967954572731077557549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3106623939430308103410065 2329967954572731077557549)
        ·
          refine ⟨873737982964774154084081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2329967954572731077557549 873737982964774154084081)
          ·
            refine ⟨655303487223580615563061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873737982964774154084081 655303487223580615563061)
            ·
              refine ⟨61434701927210682709037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 655303487223580615563061 61434701927210682709037)
              ·
                refine ⟨23038013222704006015889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61434701927210682709037 23038013222704006015889)
                ·
                  rfl

theorem cell19_75712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_75712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75712 prefixEnd_75712 := by exact prefixLift 75712
  have htrace : WordTrace (prefixWord ++ tailWord_75712) baseStart_75712 baseEnd_75712 := by
    simpa [prefixWord, tailWord_75712, baseEnd_75712] using wordTrace_append hprefix tailTrace_75712
  have hstable : (prefixWord ++ tailWord_75712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75712).length < 2 ^ (prefixWord ++ tailWord_75712).sum := by decide
  have hdescent : baseEnd_75712 < baseStart_75712 := by decide
  rcases family_descends (prefixWord ++ tailWord_75712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75752 : List Nat := [2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_75752 : Nat := 118140960795 + 75752 * 2 ^ 59
def prefixEnd_75752 : Nat := 4983230072969 + 3 ^ 40 * 75752 * 2
def baseEnd_75752 : Nat := 23050184615995765126891

theorem tailTrace_75752 : CollatzResearch.WordTrace tailWord_75752 prefixEnd_75752 23050184615995765126891 := by
  unfold tailWord_75752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381451210785458128354755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1841934947713944171139673 1381451210785458128354755)
  ·
    refine ⟨2072176816178187192532133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1381451210785458128354755 2072176816178187192532133)
    ·
      refine ⟨388533153033410098599775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2072176816178187192532133 388533153033410098599775)
      ·
        refine ⟨582799729550115147899663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388533153033410098599775 582799729550115147899663)
        ·
          refine ⟨874199594325172721849495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582799729550115147899663 874199594325172721849495)
          ·
            refine ⟨1311299391487759082774243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874199594325172721849495 1311299391487759082774243)
            ·
              refine ⟨1966949087231638624161365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311299391487759082774243 1966949087231638624161365)
              ·
                refine ⟨23050184615995765126891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1966949087231638624161365 23050184615995765126891)
                ·
                  rfl

theorem cell19_75752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_75752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75752 prefixEnd_75752 := by exact prefixLift 75752
  have htrace : WordTrace (prefixWord ++ tailWord_75752) baseStart_75752 baseEnd_75752 := by
    simpa [prefixWord, tailWord_75752, baseEnd_75752] using wordTrace_append hprefix tailTrace_75752
  have hstable : (prefixWord ++ tailWord_75752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75752).length < 2 ^ (prefixWord ++ tailWord_75752).sum := by decide
  have hdescent : baseEnd_75752 < baseStart_75752 := by decide
  rcases family_descends (prefixWord ++ tailWord_75752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75769 : List Nat := [1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_75769 : Nat := 118140960795 + 75769 * 2 ^ 59
def prefixEnd_75769 : Nat := 4983230072969 + 3 ^ 40 * 75769 * 2
def baseEnd_75769 : Nat := 23055357458144762749067

theorem tailTrace_75769 : CollatzResearch.WordTrace tailWord_75769 prefixEnd_75769 23055357458144762749067 := by
  unfold tailWord_75769
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763522462509328160078361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1842348308339552106718907 2763522462509328160078361)
  ·
    refine ⟨2072641846881996120058771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2763522462509328160078361 2072641846881996120058771)
    ·
      refine ⟨3108962770322994180088157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072641846881996120058771 3108962770322994180088157)
      ·
        refine ⟨1165861038871122817533059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3108962770322994180088157 1165861038871122817533059)
        ·
          refine ⟨1748791558306684226299589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165861038871122817533059 1748791558306684226299589)
          ·
            refine ⟨327898417182503292431173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1748791558306684226299589 327898417182503292431173)
            ·
              refine ⟨61480953221719367330845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327898417182503292431173 61480953221719367330845)
              ·
                refine ⟨23055357458144762749067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61480953221719367330845 23055357458144762749067)
                ·
                  rfl

theorem cell19_75769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_75769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75769 prefixEnd_75769 := by exact prefixLift 75769
  have htrace : WordTrace (prefixWord ++ tailWord_75769) baseStart_75769 baseEnd_75769 := by
    simpa [prefixWord, tailWord_75769, baseEnd_75769] using wordTrace_append hprefix tailTrace_75769
  have hstable : (prefixWord ++ tailWord_75769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75769).length < 2 ^ (prefixWord ++ tailWord_75769).sum := by decide
  have hdescent : baseEnd_75769 < baseStart_75769 := by decide
  rcases family_descends (prefixWord ++ tailWord_75769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75786 : List Nat := [3, 1, 2, 2, 5, 1, 5]
def baseStart_75786 : Nat := 118140960795 + 75786 * 2 ^ 59
def prefixEnd_75786 : Nat := 4983230072969 + 3 ^ 40 * 75786 * 2
def baseEnd_75786 : Nat := 7686843433431253457081

theorem tailTrace_75786 : CollatzResearch.WordTrace tailWord_75786 prefixEnd_75786 7686843433431253457081 := by
  unfold tailWord_75786
  simp only [CollatzResearch.WordTrace]
  refine ⟨691035625861935015861803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1842761668965160042298141 691035625861935015861803)
  ·
    refine ⟨1036553438792902523792705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691035625861935015861803 1036553438792902523792705)
    ·
      refine ⟨777415079094676892844529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1036553438792902523792705 777415079094676892844529)
      ·
        refine ⟨583061309321007669633397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777415079094676892844529 583061309321007669633397)
        ·
          refine ⟨54661997748844469028131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 583061309321007669633397 54661997748844469028131)
          ·
            refine ⟨81992996623266703542197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54661997748844469028131 81992996623266703542197)
            ·
              refine ⟨7686843433431253457081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81992996623266703542197 7686843433431253457081)
              ·
                rfl

theorem cell19_75786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_75786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75786 prefixEnd_75786 := by exact prefixLift 75786
  have htrace : WordTrace (prefixWord ++ tailWord_75786) baseStart_75786 baseEnd_75786 := by
    simpa [prefixWord, tailWord_75786, baseEnd_75786] using wordTrace_append hprefix tailTrace_75786
  have hstable : (prefixWord ++ tailWord_75786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75786).length < 2 ^ (prefixWord ++ tailWord_75786).sum := by decide
  have hdescent : baseEnd_75786 < baseStart_75786 := by decide
  rcases family_descends (prefixWord ++ tailWord_75786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75864 : List Nat := [2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_75864 : Nat := 118140960795 + 75864 * 2 ^ 59
def prefixEnd_75864 : Nat := 4983230072969 + 3 ^ 40 * 75864 * 2
def baseEnd_75864 : Nat := 23084264517212690637697

theorem tailTrace_75864 : CollatzResearch.WordTrace tailWord_75864 prefixEnd_75864 23084264517212690637697 := by
  unfold tailWord_75864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383493698582579692393323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1844658264776772923191097 1383493698582579692393323)
  ·
    refine ⟨2075240547873869538589985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1383493698582579692393323 2075240547873869538589985)
    ·
      refine ⟨1556430410905402153942489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2075240547873869538589985 1556430410905402153942489)
      ·
        refine ⟨1167322808179051615456867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1556430410905402153942489 1167322808179051615456867)
        ·
          refine ⟨1750984212268577423185301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167322808179051615456867 1750984212268577423185301)
          ·
            refine ⟨82077384950089566711811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1750984212268577423185301 82077384950089566711811)
            ·
              refine ⟨123116077425134350067717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82077384950089566711811 123116077425134350067717)
              ·
                refine ⟨23084264517212690637697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123116077425134350067717 23084264517212690637697)
                ·
                  rfl

theorem cell19_75864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_75864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75864 prefixEnd_75864 := by exact prefixLift 75864
  have htrace : WordTrace (prefixWord ++ tailWord_75864) baseStart_75864 baseEnd_75864 := by
    simpa [prefixWord, tailWord_75864, baseEnd_75864] using wordTrace_append hprefix tailTrace_75864
  have hstable : (prefixWord ++ tailWord_75864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75864).length < 2 ^ (prefixWord ++ tailWord_75864).sum := by decide
  have hdescent : baseEnd_75864 < baseStart_75864 := by decide
  rcases family_descends (prefixWord ++ tailWord_75864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75934 : List Nat := [4, 3, 1, 1, 4, 1, 2, 3]
def baseStart_75934 : Nat := 118140960795 + 75934 * 2 ^ 59
def prefixEnd_75934 : Nat := 4983230072969 + 3 ^ 40 * 75934 * 2
def baseEnd_75934 : Nat := 23105564455473269081951

theorem tailTrace_75934 : CollatzResearch.WordTrace tailWord_75934 prefixEnd_75934 23105564455473269081951 := by
  unfold tailWord_75934
  simp only [CollatzResearch.WordTrace]
  refine ⟨346192563363945167479357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1846360337941040893223237 346192563363945167479357)
  ·
    refine ⟨129822211261479437804759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 346192563363945167479357 129822211261479437804759)
    ·
      refine ⟨194733316892219156707139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129822211261479437804759 194733316892219156707139)
      ·
        refine ⟨292099975338328735060709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194733316892219156707139 292099975338328735060709)
        ·
          refine ⟨54768745375936637823883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292099975338328735060709 54768745375936637823883)
          ·
            refine ⟨82153118063904956735825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54768745375936637823883 82153118063904956735825)
            ·
              refine ⟨61614838547928717551869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82153118063904956735825 61614838547928717551869)
              ·
                refine ⟨23105564455473269081951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61614838547928717551869 23105564455473269081951)
                ·
                  rfl

theorem cell19_75934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_75934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75934 prefixEnd_75934 := by exact prefixLift 75934
  have htrace : WordTrace (prefixWord ++ tailWord_75934) baseStart_75934 baseEnd_75934 := by
    simpa [prefixWord, tailWord_75934, baseEnd_75934] using wordTrace_append hprefix tailTrace_75934
  have hstable : (prefixWord ++ tailWord_75934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75934).length < 2 ^ (prefixWord ++ tailWord_75934).sum := by decide
  have hdescent : baseEnd_75934 < baseStart_75934 := by decide
  rcases family_descends (prefixWord ++ tailWord_75934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75938 : List Nat := [3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_75938 : Nat := 118140960795 + 75938 * 2 ^ 59
def prefixEnd_75938 : Nat := 4983230072969 + 3 ^ 40 * 75938 * 2
def baseEnd_75938 : Nat := 23106781594802444993051

theorem tailTrace_75938 : CollatzResearch.WordTrace tailWord_75938 prefixEnd_75938 23106781594802444993051 := by
  unfold tailWord_75938
  simp only [CollatzResearch.WordTrace]
  refine ⟨692421599724267505745117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1846457599264713348653645 692421599724267505745117)
  ·
    refine ⟨259658099896600314654419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 692421599724267505745117 259658099896600314654419)
    ·
      refine ⟨389487149844900471981629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259658099896600314654419 389487149844900471981629)
      ·
        refine ⟨146057681191837676993111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389487149844900471981629 146057681191837676993111)
        ·
          refine ⟨219086521787756515489667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146057681191837676993111 219086521787756515489667)
          ·
            refine ⟨328629782681634773234501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219086521787756515489667 328629782681634773234501)
            ·
              refine ⟨61618084252806519981469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 328629782681634773234501 61618084252806519981469)
              ·
                refine ⟨23106781594802444993051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61618084252806519981469 23106781594802444993051)
                ·
                  rfl

theorem cell19_75938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_75938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75938 prefixEnd_75938 := by exact prefixLift 75938
  have htrace : WordTrace (prefixWord ++ tailWord_75938) baseStart_75938 baseEnd_75938 := by
    simpa [prefixWord, tailWord_75938, baseEnd_75938] using wordTrace_append hprefix tailTrace_75938
  have hstable : (prefixWord ++ tailWord_75938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75938).length < 2 ^ (prefixWord ++ tailWord_75938).sum := by decide
  have hdescent : baseEnd_75938 < baseStart_75938 := by decide
  rcases family_descends (prefixWord ++ tailWord_75938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75940 : List Nat := [2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_75940 : Nat := 118140960795 + 75940 * 2 ^ 59
def prefixEnd_75940 : Nat := 4983230072969 + 3 ^ 40 * 75940 * 2
def baseEnd_75940 : Nat := 23107390164467032948601

theorem tailTrace_75940 : CollatzResearch.WordTrace tailWord_75940 prefixEnd_75940 23107390164467032948601 := by
  unfold tailWord_75940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384879672444912182276637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1846506229926549576368849 1384879672444912182276637)
  ·
    refine ⟨519329877166842068353739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1384879672444912182276637 519329877166842068353739)
    ·
      refine ⟨778994815750263102530609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519329877166842068353739 778994815750263102530609)
      ·
        refine ⟨584246111812697326897957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 778994815750263102530609 584246111812697326897957)
        ·
          refine ⟨109546145964880748793367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 584246111812697326897957 109546145964880748793367)
          ·
            refine ⟨164319218947321123190051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109546145964880748793367 164319218947321123190051)
            ·
              refine ⟨246478828420981684785077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164319218947321123190051 246478828420981684785077)
              ·
                refine ⟨23107390164467032948601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246478828420981684785077 23107390164467032948601)
                ·
                  rfl

theorem cell19_75940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_75940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75940 prefixEnd_75940 := by exact prefixLift 75940
  have htrace : WordTrace (prefixWord ++ tailWord_75940) baseStart_75940 baseEnd_75940 := by
    simpa [prefixWord, tailWord_75940, baseEnd_75940] using wordTrace_append hprefix tailTrace_75940
  have hstable : (prefixWord ++ tailWord_75940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75940).length < 2 ^ (prefixWord ++ tailWord_75940).sum := by decide
  have hdescent : baseEnd_75940 < baseStart_75940 := by decide
  rcases family_descends (prefixWord ++ tailWord_75940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75957 : List Nat := [1, 3, 3, 4, 1, 2, 5]
def baseStart_75957 : Nat := 118140960795 + 75957 * 2 ^ 59
def prefixEnd_75957 : Nat := 4983230072969 + 3 ^ 40 * 75957 * 2
def baseEnd_75957 : Nat := 7704187668872010190259

theorem tailTrace_75957 : CollatzResearch.WordTrace tailWord_75957 prefixEnd_75957 7704187668872010190259 := by
  unfold tailWord_75957
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770379385828236267922125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1846919590552157511948083 2770379385828236267922125)
  ·
    refine ⟨1038892269685588600470797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2770379385828236267922125 1038892269685588600470797)
    ·
      refine ⟨389584601132095725176549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1038892269685588600470797 389584601132095725176549)
      ·
        refine ⟨73047112712267948470603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389584601132095725176549 73047112712267948470603)
        ·
          refine ⟨109570669068401922705905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73047112712267948470603 109570669068401922705905)
          ·
            refine ⟨82178001801301442029429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109570669068401922705905 82178001801301442029429)
            ·
              refine ⟨7704187668872010190259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82178001801301442029429 7704187668872010190259)
              ·
                rfl

theorem cell19_75957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_75957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75957 prefixEnd_75957 := by exact prefixLift 75957
  have htrace : WordTrace (prefixWord ++ tailWord_75957) baseStart_75957 baseEnd_75957 := by
    simpa [prefixWord, tailWord_75957, baseEnd_75957] using wordTrace_append hprefix tailTrace_75957
  have hstable : (prefixWord ++ tailWord_75957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75957).length < 2 ^ (prefixWord ++ tailWord_75957).sum := by decide
  have hdescent : baseEnd_75957 < baseStart_75957 := by decide
  rcases family_descends (prefixWord ++ tailWord_75957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75997 : List Nat := [1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_75997 : Nat := 118140960795 + 75997 * 2 ^ 59
def prefixEnd_75997 : Nat := 4983230072969 + 3 ^ 40 * 75997 * 2
def baseEnd_75997 : Nat := 23124734399907789681779

theorem tailTrace_75997 : CollatzResearch.WordTrace tailWord_75997 prefixEnd_75997 23124734399907789681779 := by
  unfold tailWord_75997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771838305683323099378245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1847892203788882066252163 2771838305683323099378245)
  ·
    refine ⟨519719682315623081133421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2771838305683323099378245 519719682315623081133421)
    ·
      refine ⟨194894880868358655425033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 519719682315623081133421 194894880868358655425033)
      ·
        refine ⟨146171160651268991568775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194894880868358655425033 146171160651268991568775)
        ·
          refine ⟨219256740976903487353163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146171160651268991568775 219256740976903487353163)
          ·
            refine ⟨328885111465355231029745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219256740976903487353163 328885111465355231029745)
            ·
              refine ⟨246663833599016423272309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328885111465355231029745 246663833599016423272309)
              ·
                refine ⟨23124734399907789681779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246663833599016423272309 23124734399907789681779)
                ·
                  rfl

theorem cell19_75997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_75997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_75997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_75997 prefixEnd_75997 := by exact prefixLift 75997
  have htrace : WordTrace (prefixWord ++ tailWord_75997) baseStart_75997 baseEnd_75997 := by
    simpa [prefixWord, tailWord_75997, baseEnd_75997] using wordTrace_append hprefix tailTrace_75997
  have hstable : (prefixWord ++ tailWord_75997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75997).length < 2 ^ (prefixWord ++ tailWord_75997).sum := by decide
  have hdescent : baseEnd_75997 < baseStart_75997 := by decide
  rcases family_descends (prefixWord ++ tailWord_75997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76018 : List Nat := [3, 2, 1, 3, 2, 8]
def baseStart_76018 : Nat := 118140960795 + 76018 * 2 ^ 59
def prefixEnd_76018 : Nat := 4983230072969 + 3 ^ 40 * 76018 * 2
def baseEnd_76018 : Nat := 2570124931265107023895

theorem tailTrace_76018 : CollatzResearch.WordTrace tailWord_76018 prefixEnd_76018 2570124931265107023895 := by
  unfold tailWord_76018
  simp only [CollatzResearch.WordTrace]
  refine ⟨693151059651810921473177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1848402825738162457261805 693151059651810921473177)
  ·
    refine ⟨519863294738858191104883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 693151059651810921473177 519863294738858191104883)
    ·
      refine ⟨779794942108287286657325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519863294738858191104883 779794942108287286657325)
      ·
        refine ⟨292423103290607732496497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 779794942108287286657325 292423103290607732496497)
        ·
          refine ⟨219317327467955799372373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292423103290607732496497 219317327467955799372373)
          ·
            refine ⟨2570124931265107023895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 219317327467955799372373 2570124931265107023895)
            ·
              rfl

theorem cell19_76018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_76018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76018 prefixEnd_76018 := by exact prefixLift 76018
  have htrace : WordTrace (prefixWord ++ tailWord_76018) baseStart_76018 baseEnd_76018 := by
    simpa [prefixWord, tailWord_76018, baseEnd_76018] using wordTrace_append hprefix tailTrace_76018
  have hstable : (prefixWord ++ tailWord_76018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76018).length < 2 ^ (prefixWord ++ tailWord_76018).sum := by decide
  have hdescent : baseEnd_76018 < baseStart_76018 := by decide
  rcases family_descends (prefixWord ++ tailWord_76018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76113 : List Nat := [1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_76113 : Nat := 118140960795 + 76113 * 2 ^ 59
def prefixEnd_76113 : Nat := 4983230072969 + 3 ^ 40 * 76113 * 2
def baseEnd_76113 : Nat := 23160031440453891103685

theorem tailTrace_76113 : CollatzResearch.WordTrace tailWord_76113 prefixEnd_76113 23160031440453891103685 := by
  unfold tailWord_76113
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776069173263074910600993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1850712782175383273733995 2776069173263074910600993)
  ·
    refine ⟨2082051879947306182950745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2776069173263074910600993 2082051879947306182950745)
    ·
      refine ⟨1561538909960479637213059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2082051879947306182950745 1561538909960479637213059)
      ·
        refine ⟨2342308364940719455819589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561538909960479637213059 2342308364940719455819589)
        ·
          refine ⟨439182818426384897966173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2342308364940719455819589 439182818426384897966173)
          ·
            refine ⟨164693556909894336737315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 439182818426384897966173 164693556909894336737315)
            ·
              refine ⟨247040335364841505105973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164693556909894336737315 247040335364841505105973)
              ·
                refine ⟨23160031440453891103685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247040335364841505105973 23160031440453891103685)
                ·
                  rfl

theorem cell19_76113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_76113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76113 prefixEnd_76113 := by exact prefixLift 76113
  have htrace : WordTrace (prefixWord ++ tailWord_76113) baseStart_76113 baseEnd_76113 := by
    simpa [prefixWord, tailWord_76113, baseEnd_76113] using wordTrace_append hprefix tailTrace_76113
  have hstable : (prefixWord ++ tailWord_76113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76113).length < 2 ^ (prefixWord ++ tailWord_76113).sum := by decide
  have hdescent : baseEnd_76113 < baseStart_76113 := by decide
  rcases family_descends (prefixWord ++ tailWord_76113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76130 : List Nat := [3, 3, 2, 1, 1, 4, 5]
def baseStart_76130 : Nat := 118140960795 + 76130 * 2 ^ 59
def prefixEnd_76130 : Nat := 4983230072969 + 3 ^ 40 * 76130 * 2
def baseEnd_76130 : Nat := 7721734760867629575287

theorem tailTrace_76130 : CollatzResearch.WordTrace tailWord_76130 prefixEnd_76130 7721734760867629575287 := by
  unfold tailWord_76130
  simp only [CollatzResearch.WordTrace]
  refine ⟨694172303550371703492461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1851126142800991209313229 694172303550371703492461)
  ·
    refine ⟨260314613831389388809673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 694172303550371703492461 260314613831389388809673)
    ·
      refine ⟨195235960373542041607255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260314613831389388809673 195235960373542041607255)
      ·
        refine ⟨292853940560313062410883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195235960373542041607255 292853940560313062410883)
        ·
          refine ⟨439280910840469593616325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292853940560313062410883 439280910840469593616325)
          ·
            refine ⟨82365170782588048803061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 439280910840469593616325 82365170782588048803061)
            ·
              refine ⟨7721734760867629575287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82365170782588048803061 7721734760867629575287)
              ·
                rfl

theorem cell19_76130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_76130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76130 prefixEnd_76130 := by exact prefixLift 76130
  have htrace : WordTrace (prefixWord ++ tailWord_76130) baseStart_76130 baseEnd_76130 := by
    simpa [prefixWord, tailWord_76130, baseEnd_76130] using wordTrace_append hprefix tailTrace_76130
  have hstable : (prefixWord ++ tailWord_76130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76130).length < 2 ^ (prefixWord ++ tailWord_76130).sum := by decide
  have hdescent : baseEnd_76130 < baseStart_76130 := by decide
  rcases family_descends (prefixWord ++ tailWord_76130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76149 : List Nat := [1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_76149 : Nat := 118140960795 + 76149 * 2 ^ 59
def prefixEnd_76149 : Nat := 4983230072969 + 3 ^ 40 * 76149 * 2
def baseEnd_76149 : Nat := 23170985694416474303587

theorem tailTrace_76149 : CollatzResearch.WordTrace tailWord_76149 prefixEnd_76149 23170985694416474303587 := by
  unfold tailWord_76149
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777382201132653058911501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1851588134088435372607667 2777382201132653058911501)
  ·
    refine ⟨1041518325424744897091813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2777382201132653058911501 1041518325424744897091813)
    ·
      refine ⟨195284686017139668204715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1041518325424744897091813 195284686017139668204715)
      ·
        refine ⟨292927029025709502307073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195284686017139668204715 292927029025709502307073)
        ·
          refine ⟨219695271769282126730305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292927029025709502307073 219695271769282126730305)
          ·
            refine ⟨164771453826961595047729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219695271769282126730305 164771453826961595047729)
            ·
              refine ⟨123578590370221196285797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164771453826961595047729 123578590370221196285797)
              ·
                refine ⟨23170985694416474303587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123578590370221196285797 23170985694416474303587)
                ·
                  rfl

theorem cell19_76149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_76149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76149 prefixEnd_76149 := by exact prefixLift 76149
  have htrace : WordTrace (prefixWord ++ tailWord_76149) baseStart_76149 baseEnd_76149 := by
    simpa [prefixWord, tailWord_76149, baseEnd_76149] using wordTrace_append hprefix tailTrace_76149
  have hstable : (prefixWord ++ tailWord_76149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76149).length < 2 ^ (prefixWord ++ tailWord_76149).sum := by decide
  have hdescent : baseEnd_76149 < baseStart_76149 := by decide
  rcases family_descends (prefixWord ++ tailWord_76149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76189 : List Nat := [1, 4, 2, 1, 4, 7]
def baseStart_76189 : Nat := 118140960795 + 76189 * 2 ^ 59
def prefixEnd_76189 : Nat := 4983230072969 + 3 ^ 40 * 76189 * 2
def baseEnd_76189 : Nat := 2575906343078692601621

theorem tailTrace_76189 : CollatzResearch.WordTrace tailWord_76189 prefixEnd_76189 2575906343078692601621 := by
  unfold tailWord_76189
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778841120987739890367621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1852560747325159926911747 2778841120987739890367621)
  ·
    refine ⟨521032710185201229443929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2778841120987739890367621 521032710185201229443929)
    ·
      refine ⟨390774532638900922082947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 521032710185201229443929 390774532638900922082947)
      ·
        refine ⟨586161798958351383124421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390774532638900922082947 586161798958351383124421)
        ·
          refine ⟨109905337304690884335829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 586161798958351383124421 109905337304690884335829)
          ·
            refine ⟨2575906343078692601621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 109905337304690884335829 2575906343078692601621)
            ·
              rfl

theorem cell19_76189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_76189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76189 prefixEnd_76189 := by exact prefixLift 76189
  have htrace : WordTrace (prefixWord ++ tailWord_76189) baseStart_76189 baseEnd_76189 := by
    simpa [prefixWord, tailWord_76189, baseEnd_76189] using wordTrace_append hprefix tailTrace_76189
  have hstable : (prefixWord ++ tailWord_76189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76189).length < 2 ^ (prefixWord ++ tailWord_76189).sum := by decide
  have hdescent : baseEnd_76189 < baseStart_76189 := by decide
  rcases family_descends (prefixWord ++ tailWord_76189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76267 : List Nat := [1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_76267 : Nat := 118140960795 + 76267 * 2 ^ 59
def prefixEnd_76267 : Nat := 4983230072969 + 3 ^ 40 * 76267 * 2
def baseEnd_76267 : Nat := 23206891304627163681043

theorem tailTrace_76267 : CollatzResearch.WordTrace tailWord_76267 prefixEnd_76267 23206891304627163681043 := by
  unfold tailWord_76267
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781686014705159211707055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1854457343136772807804703 2781686014705159211707055)
  ·
    refine ⟨4172529022057738817560583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2781686014705159211707055 4172529022057738817560583)
    ·
      refine ⟨6258793533086608226340875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172529022057738817560583 6258793533086608226340875)
      ·
        refine ⟨9388190299629912339511313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6258793533086608226340875 9388190299629912339511313)
        ·
          refine ⟨7041142724722434254633485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9388190299629912339511313 7041142724722434254633485)
          ·
            refine ⟨2640428521770912845487557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7041142724722434254633485 2640428521770912845487557)
            ·
              refine ⟨495080347832046158528917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2640428521770912845487557 495080347832046158528917)
              ·
                refine ⟨23206891304627163681043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 495080347832046158528917 23206891304627163681043)
                ·
                  rfl

theorem cell19_76267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_76267 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76267 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76267 prefixEnd_76267 := by exact prefixLift 76267
  have htrace : WordTrace (prefixWord ++ tailWord_76267) baseStart_76267 baseEnd_76267 := by
    simpa [prefixWord, tailWord_76267, baseEnd_76267] using wordTrace_append hprefix tailTrace_76267
  have hstable : (prefixWord ++ tailWord_76267).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76267).length < 2 ^ (prefixWord ++ tailWord_76267).sum := by decide
  have hdescent : baseEnd_76267 < baseStart_76267 := by decide
  rcases family_descends (prefixWord ++ tailWord_76267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76320 : List Nat := [2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_76320 : Nat := 118140960795 + 76320 * 2 ^ 59
def prefixEnd_76320 : Nat := 4983230072969 + 3 ^ 40 * 76320 * 2
def baseEnd_76320 : Nat := 23223018400738744503121

theorem tailTrace_76320 : CollatzResearch.WordTrace tailWord_76320 prefixEnd_76320 23223018400738744503121 := by
  unfold tailWord_76320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391809541756574631693207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1855746055675432842257609 1391809541756574631693207)
  ·
    refine ⟨2087714312634861947539811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1391809541756574631693207 2087714312634861947539811)
    ·
      refine ⟨3131571468952292921309717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087714312634861947539811 3131571468952292921309717)
      ·
        refine ⟨146792412607138730686393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3131571468952292921309717 146792412607138730686393)
        ·
          refine ⟨110094309455354048014795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146792412607138730686393 110094309455354048014795)
          ·
            refine ⟨165141464183031072022193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110094309455354048014795 165141464183031072022193)
            ·
              refine ⟨123856098137273304016645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165141464183031072022193 123856098137273304016645)
              ·
                refine ⟨23223018400738744503121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123856098137273304016645 23223018400738744503121)
                ·
                  rfl

theorem cell19_76320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_76320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76320 prefixEnd_76320 := by exact prefixLift 76320
  have htrace : WordTrace (prefixWord ++ tailWord_76320) baseStart_76320 baseEnd_76320 := by
    simpa [prefixWord, tailWord_76320, baseEnd_76320] using wordTrace_append hprefix tailTrace_76320
  have hstable : (prefixWord ++ tailWord_76320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76320).length < 2 ^ (prefixWord ++ tailWord_76320).sum := by decide
  have hdescent : baseEnd_76320 < baseStart_76320 := by decide
  rcases family_descends (prefixWord ++ tailWord_76320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76343 : List Nat := [1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_76343 : Nat := 118140960795 + 76343 * 2 ^ 59
def prefixEnd_76343 : Nat := 4983230072969 + 3 ^ 40 * 76343 * 2
def baseEnd_76343 : Nat := 23230016951881505991947

theorem tailTrace_76343 : CollatzResearch.WordTrace tailWord_76343 prefixEnd_76343 23230016951881505991947 := by
  unfold tailWord_76343
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784457962429824191473683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1856305308286549460982455 2784457962429824191473683)
  ·
    refine ⟨4176686943644736287210525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2784457962429824191473683 4176686943644736287210525)
    ·
      refine ⟨1566257603866776107703947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4176686943644736287210525 1566257603866776107703947)
      ·
        refine ⟨2349386405800164161555921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566257603866776107703947 2349386405800164161555921)
        ·
          refine ⟨1762039804350123121166941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2349386405800164161555921 1762039804350123121166941)
          ·
            refine ⟨660764926631296170437603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1762039804350123121166941 660764926631296170437603)
            ·
              refine ⟨991147389946944255656405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660764926631296170437603 991147389946944255656405)
              ·
                refine ⟨23230016951881505991947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 991147389946944255656405 23230016951881505991947)
                ·
                  rfl

theorem cell19_76343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_76343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76343 prefixEnd_76343 := by exact prefixLift 76343
  have htrace : WordTrace (prefixWord ++ tailWord_76343) baseStart_76343 baseEnd_76343 := by
    simpa [prefixWord, tailWord_76343, baseEnd_76343] using wordTrace_append hprefix tailTrace_76343
  have hstable : (prefixWord ++ tailWord_76343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76343).length < 2 ^ (prefixWord ++ tailWord_76343).sum := by decide
  have hdescent : baseEnd_76343 < baseStart_76343 := by decide
  rcases family_descends (prefixWord ++ tailWord_76343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76356 : List Nat := [2, 3, 5, 1, 1, 7]
def baseStart_76356 : Nat := 118140960795 + 76356 * 2 ^ 59
def prefixEnd_76356 : Nat := 4983230072969 + 3 ^ 40 * 76356 * 2
def baseEnd_76356 : Nat := 2581552517189036411447

theorem tailTrace_76356 : CollatzResearch.WordTrace tailWord_76356 prefixEnd_76356 2581552517189036411447 := by
  unfold tailWord_76356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392466055691363705848461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1856621407588484941131281 1392466055691363705848461)
  ·
    refine ⟨522174770884261389693173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1392466055691363705848461 522174770884261389693173)
    ·
      refine ⟨48953884770399505283735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 522174770884261389693173 48953884770399505283735)
      ·
        refine ⟨73430827155599257925603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48953884770399505283735 73430827155599257925603)
        ·
          refine ⟨110146240733398886888405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73430827155599257925603 110146240733398886888405)
          ·
            refine ⟨2581552517189036411447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110146240733398886888405 2581552517189036411447)
            ·
              rfl

theorem cell19_76356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_76356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76356 prefixEnd_76356 := by exact prefixLift 76356
  have htrace : WordTrace (prefixWord ++ tailWord_76356) baseStart_76356 baseEnd_76356 := by
    simpa [prefixWord, tailWord_76356, baseEnd_76356] using wordTrace_append hprefix tailTrace_76356
  have hstable : (prefixWord ++ tailWord_76356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76356).length < 2 ^ (prefixWord ++ tailWord_76356).sum := by decide
  have hdescent : baseEnd_76356 < baseStart_76356 := by decide
  rcases family_descends (prefixWord ++ tailWord_76356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76358 : List Nat := [6, 1, 1, 1, 2, 8]
def baseStart_76358 : Nat := 118140960795 + 76358 * 2 ^ 59
def prefixEnd_76358 : Nat := 4983230072969 + 3 ^ 40 * 76358 * 2
def baseEnd_76358 : Nat := 2581620136040657295397

theorem tailTrace_76358 : CollatzResearch.WordTrace tailWord_76358 prefixEnd_76358 2581620136040657295397 := by
  unfold tailWord_76358
  simp only [CollatzResearch.WordTrace]
  refine ⟨87031408042983804789679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1856670038250321168846485 87031408042983804789679)
  ·
    refine ⟨130547112064475707184519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87031408042983804789679 130547112064475707184519)
    ·
      refine ⟨195820668096713560776779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130547112064475707184519 195820668096713560776779)
      ·
        refine ⟨293731002145070341165169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195820668096713560776779 293731002145070341165169)
        ·
          refine ⟨220298251608802755873877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293731002145070341165169 220298251608802755873877)
          ·
            refine ⟨2581620136040657295397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 220298251608802755873877 2581620136040657295397)
            ·
              rfl

theorem cell19_76358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_76358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76358 prefixEnd_76358 := by exact prefixLift 76358
  have htrace : WordTrace (prefixWord ++ tailWord_76358) baseStart_76358 baseEnd_76358 := by
    simpa [prefixWord, tailWord_76358, baseEnd_76358] using wordTrace_append hprefix tailTrace_76358
  have hstable : (prefixWord ++ tailWord_76358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76358).length < 2 ^ (prefixWord ++ tailWord_76358).sum := by decide
  have hdescent : baseEnd_76358 < baseStart_76358 := by decide
  rcases family_descends (prefixWord ++ tailWord_76358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76362 : List Nat := [3, 1, 2, 1, 1, 11]
def baseStart_76362 : Nat := 118140960795 + 76362 * 2 ^ 59
def prefixEnd_76362 : Nat := 4983230072969 + 3 ^ 40 * 76362 * 2
def baseEnd_76362 : Nat := 2581755373743899063297

theorem tailTrace_76362 : CollatzResearch.WordTrace tailWord_76362 prefixEnd_76362 2581755373743899063297 := by
  unfold tailWord_76362
  simp only [CollatzResearch.WordTrace]
  refine ⟨696287737340247609103835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1856767299573993624276893 696287737340247609103835)
  ·
    refine ⟨1044431606010371413655753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696287737340247609103835 1044431606010371413655753)
    ·
      refine ⟨783323704507778560241815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1044431606010371413655753 783323704507778560241815)
      ·
        refine ⟨1174985556761667840362723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783323704507778560241815 1174985556761667840362723)
        ·
          refine ⟨1762478335142501760544085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174985556761667840362723 1762478335142501760544085)
          ·
            refine ⟨2581755373743899063297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1762478335142501760544085 2581755373743899063297)
            ·
              rfl

theorem cell19_76362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_76362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76362 prefixEnd_76362 := by exact prefixLift 76362
  have htrace : WordTrace (prefixWord ++ tailWord_76362) baseStart_76362 baseEnd_76362 := by
    simpa [prefixWord, tailWord_76362, baseEnd_76362] using wordTrace_append hprefix tailTrace_76362
  have hstable : (prefixWord ++ tailWord_76362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76362).length < 2 ^ (prefixWord ++ tailWord_76362).sum := by decide
  have hdescent : baseEnd_76362 < baseStart_76362 := by decide
  rcases family_descends (prefixWord ++ tailWord_76362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76470 : List Nat := [5, 1, 3, 1, 2, 2, 5]
def baseStart_76470 : Nat := 118140960795 + 76470 * 2 ^ 59
def prefixEnd_76470 : Nat := 4983230072969 + 3 ^ 40 * 76470 * 2
def baseEnd_76470 : Nat := 7756220375194280389793

theorem tailTrace_76470 : CollatzResearch.WordTrace tailWord_76470 prefixEnd_76470 7756220375194280389793 := by
  unfold tailWord_76470
  simp only [CollatzResearch.WordTrace]
  refine ⟨174318127060607805084179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1859393355313149920897909 174318127060607805084179)
  ·
    refine ⟨261477190590911707626269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174318127060607805084179 261477190590911707626269)
    ·
      refine ⟨98053946471591890359851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261477190590911707626269 98053946471591890359851)
      ·
        refine ⟨147080919707387835539777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98053946471591890359851 147080919707387835539777)
        ·
          refine ⟨110310689780540876654833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147080919707387835539777 110310689780540876654833)
          ·
            refine ⟨82733017335405657491125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110310689780540876654833 82733017335405657491125)
            ·
              refine ⟨7756220375194280389793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82733017335405657491125 7756220375194280389793)
              ·
                rfl

theorem cell19_76470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_76470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76470 prefixEnd_76470 := by exact prefixLift 76470
  have htrace : WordTrace (prefixWord ++ tailWord_76470) baseStart_76470 baseEnd_76470 := by
    simpa [prefixWord, tailWord_76470, baseEnd_76470] using wordTrace_append hprefix tailTrace_76470
  have hstable : (prefixWord ++ tailWord_76470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76470).length < 2 ^ (prefixWord ++ tailWord_76470).sum := by decide
  have hdescent : baseEnd_76470 < baseStart_76470 := by decide
  rcases family_descends (prefixWord ++ tailWord_76470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76567 : List Nat := [1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_76567 : Nat := 118140960795 + 76567 * 2 ^ 59
def prefixEnd_76567 : Nat := 4983230072969 + 3 ^ 40 * 76567 * 2
def baseEnd_76567 : Nat := 23298176754315357013559

theorem tailTrace_76567 : CollatzResearch.WordTrace tailWord_76567 prefixEnd_76567 23298176754315357013559 := by
  unfold tailWord_76567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2792627913618310447627955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1861751942412206965085303 2792627913618310447627955)
  ·
    refine ⟨4188941870427465671441933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2792627913618310447627955 4188941870427465671441933)
    ·
      refine ⟨1570853201410299626790725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4188941870427465671441933 1570853201410299626790725)
      ·
        refine ⟨294534975264431180023261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1570853201410299626790725 294534975264431180023261)
        ·
          refine ⟨110450615724161692508723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294534975264431180023261 110450615724161692508723)
          ·
            refine ⟨165675923586242538763085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110450615724161692508723 165675923586242538763085)
            ·
              refine ⟨62128471344840952036157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165675923586242538763085 62128471344840952036157)
              ·
                refine ⟨23298176754315357013559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62128471344840952036157 23298176754315357013559)
                ·
                  rfl

theorem cell19_76567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_76567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76567 prefixEnd_76567 := by exact prefixLift 76567
  have htrace : WordTrace (prefixWord ++ tailWord_76567) baseStart_76567 baseEnd_76567 := by
    simpa [prefixWord, tailWord_76567, baseEnd_76567] using wordTrace_append hprefix tailTrace_76567
  have hstable : (prefixWord ++ tailWord_76567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76567).length < 2 ^ (prefixWord ++ tailWord_76567).sum := by decide
  have hdescent : baseEnd_76567 < baseStart_76567 := by decide
  rcases family_descends (prefixWord ++ tailWord_76567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76586 : List Nat := [3, 1, 4, 3, 1, 1, 6]
def baseStart_76586 : Nat := 118140960795 + 76586 * 2 ^ 59
def prefixEnd_76586 : Nat := 4983230072969 + 3 ^ 40 * 76586 * 2
def baseEnd_76586 : Nat := 7767986055376314197095

theorem tailTrace_76586 : CollatzResearch.WordTrace tailWord_76586 prefixEnd_76586 7767986055376314197095 := by
  unfold tailWord_76586
  simp only [CollatzResearch.WordTrace]
  refine ⟨698330225137369173142403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1862213933699651128379741 698330225137369173142403)
  ·
    refine ⟨1047495337706053759713605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698330225137369173142403 1047495337706053759713605)
    ·
      refine ⟨196405375819885079946301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1047495337706053759713605 196405375819885079946301)
      ·
        refine ⟨73652015932456904979863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196405375819885079946301 73652015932456904979863)
        ·
          refine ⟨110478023898685357469795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73652015932456904979863 110478023898685357469795)
          ·
            refine ⟨165717035848028036204693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110478023898685357469795 165717035848028036204693)
            ·
              refine ⟨7767986055376314197095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165717035848028036204693 7767986055376314197095)
              ·
                rfl

theorem cell19_76586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_76586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76586 prefixEnd_76586 := by exact prefixLift 76586
  have htrace : WordTrace (prefixWord ++ tailWord_76586) baseStart_76586 baseEnd_76586 := by
    simpa [prefixWord, tailWord_76586, baseEnd_76586] using wordTrace_append hprefix tailTrace_76586
  have hstable : (prefixWord ++ tailWord_76586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76586).length < 2 ^ (prefixWord ++ tailWord_76586).sum := by decide
  have hdescent : baseEnd_76586 < baseStart_76586 := by decide
  rcases family_descends (prefixWord ++ tailWord_76586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76647 : List Nat := [1, 1, 5, 1, 2, 2, 7]
def baseStart_76647 : Nat := 118140960795 + 76647 * 2 ^ 59
def prefixEnd_76647 : Nat := 4983230072969 + 3 ^ 40 * 76647 * 2
def baseEnd_76647 : Nat := 7774173180299625078521

theorem tailTrace_76647 : CollatzResearch.WordTrace tailWord_76647 prefixEnd_76647 7774173180299625078521 := by
  unfold tailWord_76647
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795545753328484110540195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1863697168885656073693463 2795545753328484110540195)
  ·
    refine ⟨4193318629992726165810293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2795545753328484110540195 4193318629992726165810293)
    ·
      refine ⟨393123621561818078044715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4193318629992726165810293 393123621561818078044715)
      ·
        refine ⟨589685432342727117067073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393123621561818078044715 589685432342727117067073)
        ·
          refine ⟨442264074257045337800305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589685432342727117067073 442264074257045337800305)
          ·
            refine ⟨331698055692784003350229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442264074257045337800305 331698055692784003350229)
            ·
              refine ⟨7774173180299625078521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 331698055692784003350229 7774173180299625078521)
              ·
                rfl

theorem cell19_76647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_76647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76647 prefixEnd_76647 := by exact prefixLift 76647
  have htrace : WordTrace (prefixWord ++ tailWord_76647) baseStart_76647 baseEnd_76647 := by
    simpa [prefixWord, tailWord_76647, baseEnd_76647] using wordTrace_append hprefix tailTrace_76647
  have hstable : (prefixWord ++ tailWord_76647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76647).length < 2 ^ (prefixWord ++ tailWord_76647).sum := by decide
  have hdescent : baseEnd_76647 < baseStart_76647 := by decide
  rcases family_descends (prefixWord ++ tailWord_76647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76662 : List Nat := [5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_76662 : Nat := 118140960795 + 76662 * 2 ^ 59
def prefixEnd_76662 : Nat := 4983230072969 + 3 ^ 40 * 76662 * 2
def baseEnd_76662 : Nat := 23327083813383284902189

theorem tailTrace_76662 : CollatzResearch.WordTrace tailWord_76662 prefixEnd_76662 23327083813383284902189 := by
  unfold tailWord_76662
  simp only [CollatzResearch.WordTrace]
  refine ⟨174755803017133854521015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1864061898849427781557493 174755803017133854521015)
  ·
    refine ⟨262133704525700781781523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174755803017133854521015 262133704525700781781523)
    ·
      refine ⟨393200556788551172672285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262133704525700781781523 393200556788551172672285)
      ·
        refine ⟨147450208795706689752107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393200556788551172672285 147450208795706689752107)
        ·
          refine ⟨221175313193560034628161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147450208795706689752107 221175313193560034628161)
          ·
            refine ⟨165881484895170025971121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221175313193560034628161 165881484895170025971121)
            ·
              refine ⟨124411113671377519478341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165881484895170025971121 124411113671377519478341)
              ·
                refine ⟨23327083813383284902189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124411113671377519478341 23327083813383284902189)
                ·
                  rfl

theorem cell19_76662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_76662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76662 prefixEnd_76662 := by exact prefixLift 76662
  have htrace : WordTrace (prefixWord ++ tailWord_76662) baseStart_76662 baseEnd_76662 := by
    simpa [prefixWord, tailWord_76662, baseEnd_76662] using wordTrace_append hprefix tailTrace_76662
  have hstable : (prefixWord ++ tailWord_76662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76662).length < 2 ^ (prefixWord ++ tailWord_76662).sum := by decide
  have hdescent : baseEnd_76662 < baseStart_76662 := by decide
  rcases family_descends (prefixWord ++ tailWord_76662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76717 : List Nat := [1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_76717 : Nat := 118140960795 + 76717 * 2 ^ 59
def prefixEnd_76717 : Nat := 4983230072969 + 3 ^ 40 * 76717 * 2
def baseEnd_76717 : Nat := 23343819479159453679817

theorem tailTrace_76717 : CollatzResearch.WordTrace tailWord_76717 prefixEnd_76717 23343819479159453679817 := by
  unfold tailWord_76717
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798098863074886065588405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1865399242049924043725603 2798098863074886065588405)
  ·
    refine ⟨262321768413270568648913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2798098863074886065588405 262321768413270568648913)
    ·
      refine ⟨196741326309952926486685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262321768413270568648913 196741326309952926486685)
      ·
        refine ⟨73777997366232347432507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196741326309952926486685 73777997366232347432507)
        ·
          refine ⟨110666996049348521148761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73777997366232347432507 110666996049348521148761)
          ·
            refine ⟨83000247037011390861571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110666996049348521148761 83000247037011390861571)
            ·
              refine ⟨124500370555517086292357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83000247037011390861571 124500370555517086292357)
              ·
                refine ⟨23343819479159453679817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124500370555517086292357 23343819479159453679817)
                ·
                  rfl

theorem cell19_76717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_76717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76717 prefixEnd_76717 := by exact prefixLift 76717
  have htrace : WordTrace (prefixWord ++ tailWord_76717) baseStart_76717 baseEnd_76717 := by
    simpa [prefixWord, tailWord_76717, baseEnd_76717] using wordTrace_append hprefix tailTrace_76717
  have hstable : (prefixWord ++ tailWord_76717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76717).length < 2 ^ (prefixWord ++ tailWord_76717).sum := by decide
  have hdescent : baseEnd_76717 < baseStart_76717 := by decide
  rcases family_descends (prefixWord ++ tailWord_76717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76761 : List Nat := [1, 2, 1, 2, 5, 2, 6]
def baseStart_76761 : Nat := 118140960795 + 76761 * 2 ^ 59
def prefixEnd_76761 : Nat := 4983230072969 + 3 ^ 40 * 76761 * 2
def baseEnd_76761 : Nat := 7785736003926796233973

theorem tailTrace_76761 : CollatzResearch.WordTrace tailWord_76761 prefixEnd_76761 7785736003926796233973 := by
  unfold tailWord_76761
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799703674915481580190137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1866469116610321053460091 2799703674915481580190137)
  ·
    refine ⟨2099777756186611185142603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2799703674915481580190137 2099777756186611185142603)
    ·
      refine ⟨3149666634279916777713905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099777756186611185142603 3149666634279916777713905)
      ·
        refine ⟨2362249975709937583285429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3149666634279916777713905 2362249975709937583285429)
        ·
          refine ⟨221460935222806648433009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2362249975709937583285429 221460935222806648433009)
          ·
            refine ⟨166095701417104986324757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221460935222806648433009 166095701417104986324757)
            ·
              refine ⟨7785736003926796233973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166095701417104986324757 7785736003926796233973)
              ·
                rfl

theorem cell19_76761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_76761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76761 prefixEnd_76761 := by exact prefixLift 76761
  have htrace : WordTrace (prefixWord ++ tailWord_76761) baseStart_76761 baseEnd_76761 := by
    simpa [prefixWord, tailWord_76761, baseEnd_76761] using wordTrace_append hprefix tailTrace_76761
  have hstable : (prefixWord ++ tailWord_76761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76761).length < 2 ^ (prefixWord ++ tailWord_76761).sum := by decide
  have hdescent : baseEnd_76761 < baseStart_76761 := by decide
  rcases family_descends (prefixWord ++ tailWord_76761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76837 : List Nat := [1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_76837 : Nat := 118140960795 + 76837 * 2 ^ 59
def prefixEnd_76837 : Nat := 4983230072969 + 3 ^ 40 * 76837 * 2
def baseEnd_76837 : Nat := 23380333659034731012823

theorem tailTrace_76837 : CollatzResearch.WordTrace tailWord_76837 prefixEnd_76837 23380333659034731012823 := by
  unfold tailWord_76837
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802475622640146559956765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1868317081760097706637843 2802475622640146559956765)
  ·
    refine ⟨1050928358490054959983787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2802475622640146559956765 1050928358490054959983787)
    ·
      refine ⟨1576392537735082439975681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050928358490054959983787 1576392537735082439975681)
      ·
        refine ⟨1182294403301311829981761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576392537735082439975681 1182294403301311829981761)
        ·
          refine ⟨886720802475983872486321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182294403301311829981761 886720802475983872486321)
          ·
            refine ⟨665040601856987904364741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886720802475983872486321 665040601856987904364741)
            ·
              refine ⟨124695112848185232068389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 665040601856987904364741 124695112848185232068389)
              ·
                refine ⟨23380333659034731012823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124695112848185232068389 23380333659034731012823)
                ·
                  rfl

theorem cell19_76837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_76837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76837 prefixEnd_76837 := by exact prefixLift 76837
  have htrace : WordTrace (prefixWord ++ tailWord_76837) baseStart_76837 baseEnd_76837 := by
    simpa [prefixWord, tailWord_76837, baseEnd_76837] using wordTrace_append hprefix tailTrace_76837
  have hstable : (prefixWord ++ tailWord_76837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76837).length < 2 ^ (prefixWord ++ tailWord_76837).sum := by decide
  have hdescent : baseEnd_76837 < baseStart_76837 := by decide
  rcases family_descends (prefixWord ++ tailWord_76837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76854 : List Nat := [5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_76854 : Nat := 118140960795 + 76854 * 2 ^ 59
def prefixEnd_76854 : Nat := 4983230072969 + 3 ^ 40 * 76854 * 2
def baseEnd_76854 : Nat := 23385506501183728634999

theorem tailTrace_76854 : CollatzResearch.WordTrace tailWord_76854 prefixEnd_76854 23385506501183728634999 := by
  unfold tailWord_76854
  simp only [CollatzResearch.WordTrace]
  refine ⟨175193478973659903957851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1868730442385705642217077 175193478973659903957851)
  ·
    refine ⟨262790218460489855936777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175193478973659903957851 262790218460489855936777)
    ·
      refine ⟨197092663845367391952583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262790218460489855936777 197092663845367391952583)
      ·
        refine ⟨295638995768051087928875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197092663845367391952583 295638995768051087928875)
        ·
          refine ⟨443458493652076631893313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295638995768051087928875 443458493652076631893313)
          ·
            refine ⟨332593870239057473919985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443458493652076631893313 332593870239057473919985)
            ·
              refine ⟨249445402679293105439989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332593870239057473919985 249445402679293105439989)
              ·
                refine ⟨23385506501183728634999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249445402679293105439989 23385506501183728634999)
                ·
                  rfl

theorem cell19_76854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_76854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76854 prefixEnd_76854 := by exact prefixLift 76854
  have htrace : WordTrace (prefixWord ++ tailWord_76854) baseStart_76854 baseEnd_76854 := by
    simpa [prefixWord, tailWord_76854, baseEnd_76854] using wordTrace_append hprefix tailTrace_76854
  have hstable : (prefixWord ++ tailWord_76854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76854).length < 2 ^ (prefixWord ++ tailWord_76854).sum := by decide
  have hdescent : baseEnd_76854 < baseStart_76854 := by decide
  rcases family_descends (prefixWord ++ tailWord_76854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76856 : List Nat := [2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_76856 : Nat := 118140960795 + 76856 * 2 ^ 59
def prefixEnd_76856 : Nat := 4983230072969 + 3 ^ 40 * 76856 * 2
def baseEnd_76856 : Nat := 23386115070848316590549

theorem tailTrace_76856 : CollatzResearch.WordTrace tailWord_76856 prefixEnd_76856 23386115070848316590549 := by
  unfold tailWord_76856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401584304785656402449211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1868779073047541869932281 1401584304785656402449211)
  ·
    refine ⟨2102376457178484603673817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1401584304785656402449211 2102376457178484603673817)
    ·
      refine ⟨1576782342883863452755363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2102376457178484603673817 1576782342883863452755363)
      ·
        refine ⟨2365173514325795179133045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576782342883863452755363 2365173514325795179133045)
        ·
          refine ⟨221735016968043298043723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2365173514325795179133045 221735016968043298043723)
          ·
            refine ⟨332602525452064947065585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221735016968043298043723 332602525452064947065585)
            ·
              refine ⟨249451894089048710299189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332602525452064947065585 249451894089048710299189)
              ·
                refine ⟨23386115070848316590549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249451894089048710299189 23386115070848316590549)
                ·
                  rfl

theorem cell19_76856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_76856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76856 prefixEnd_76856 := by exact prefixLift 76856
  have htrace : WordTrace (prefixWord ++ tailWord_76856) baseStart_76856 baseEnd_76856 := by
    simpa [prefixWord, tailWord_76856, baseEnd_76856] using wordTrace_append hprefix tailTrace_76856
  have hstable : (prefixWord ++ tailWord_76856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76856).length < 2 ^ (prefixWord ++ tailWord_76856).sum := by decide
  have hdescent : baseEnd_76856 < baseStart_76856 := by decide
  rcases family_descends (prefixWord ++ tailWord_76856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76886 : List Nat := [5, 2, 2, 1, 3, 1, 1, 4]
def baseStart_76886 : Nat := 118140960795 + 76886 * 2 ^ 59
def prefixEnd_76886 : Nat := 4983230072969 + 3 ^ 40 * 76886 * 2
def baseEnd_76886 : Nat := 23395243615817135923801

theorem tailTrace_76886 : CollatzResearch.WordTrace tailWord_76886 prefixEnd_76886 23395243615817135923801 := by
  unfold tailWord_76886
  simp only [CollatzResearch.WordTrace]
  refine ⟨175266424966414245530657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1869508532975085285660341 175266424966414245530657)
  ·
    refine ⟨131449818724810684147993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175266424966414245530657 131449818724810684147993)
    ·
      refine ⟨98587364043608013110995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131449818724810684147993 98587364043608013110995)
      ·
        refine ⟨147881046065412019666493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98587364043608013110995 147881046065412019666493)
        ·
          refine ⟨55455392274529507374935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147881046065412019666493 55455392274529507374935)
          ·
            refine ⟨83183088411794261062403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55455392274529507374935 83183088411794261062403)
            ·
              refine ⟨124774632617691391593605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83183088411794261062403 124774632617691391593605)
              ·
                refine ⟨23395243615817135923801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124774632617691391593605 23395243615817135923801)
                ·
                  rfl

theorem cell19_76886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_76886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76886 prefixEnd_76886 := by exact prefixLift 76886
  have htrace : WordTrace (prefixWord ++ tailWord_76886) baseStart_76886 baseEnd_76886 := by
    simpa [prefixWord, tailWord_76886, baseEnd_76886] using wordTrace_append hprefix tailTrace_76886
  have hstable : (prefixWord ++ tailWord_76886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76886).length < 2 ^ (prefixWord ++ tailWord_76886).sum := by decide
  have hdescent : baseEnd_76886 < baseStart_76886 := by decide
  rcases family_descends (prefixWord ++ tailWord_76886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76926 : List Nat := [4, 2, 4, 1, 1, 1, 6]
def baseStart_76926 : Nat := 118140960795 + 76926 * 2 ^ 59
def prefixEnd_76926 : Nat := 4983230072969 + 3 ^ 40 * 76926 * 2
def baseEnd_76926 : Nat := 7802471669702965011601

theorem tailTrace_76926 : CollatzResearch.WordTrace tailWord_76926 prefixEnd_76926 7802471669702965011601 := by
  unfold tailWord_76926
  simp only [CollatzResearch.WordTrace]
  refine ⟨350715214914714344993329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1870481146211809839964421 350715214914714344993329)
  ·
    refine ⟨263036411186035758744997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 350715214914714344993329 263036411186035758744997)
    ·
      refine ⟨49319327097381704764687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263036411186035758744997 49319327097381704764687)
      ·
        refine ⟨73978990646072557147031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49319327097381704764687 73978990646072557147031)
        ·
          refine ⟨110968485969108835720547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73978990646072557147031 110968485969108835720547)
          ·
            refine ⟨166452728953663253580821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110968485969108835720547 166452728953663253580821)
            ·
              refine ⟨7802471669702965011601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166452728953663253580821 7802471669702965011601)
              ·
                rfl

theorem cell19_76926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_76926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76926 prefixEnd_76926 := by exact prefixLift 76926
  have htrace : WordTrace (prefixWord ++ tailWord_76926) baseStart_76926 baseEnd_76926 := by
    simpa [prefixWord, tailWord_76926, baseEnd_76926] using wordTrace_append hprefix tailTrace_76926
  have hstable : (prefixWord ++ tailWord_76926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76926).length < 2 ^ (prefixWord ++ tailWord_76926).sum := by decide
  have hdescent : baseEnd_76926 < baseStart_76926 := by decide
  rcases family_descends (prefixWord ++ tailWord_76926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76932 : List Nat := [2, 3, 2, 1, 2, 3, 6]
def baseStart_76932 : Nat := 118140960795 + 76932 * 2 ^ 59
def prefixEnd_76932 : Nat := 4983230072969 + 3 ^ 40 * 76932 * 2
def baseEnd_76932 : Nat := 7803080239367552967151

theorem tailTrace_76932 : CollatzResearch.WordTrace tailWord_76932 prefixEnd_76932 7803080239367552967151 := by
  unfold tailWord_76932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402970278647988892332525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1870627038197318523110033 1402970278647988892332525)
  ·
    refine ⟨526113854492995834624697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1402970278647988892332525 526113854492995834624697)
    ·
      refine ⟨394585390869746875968523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 526113854492995834624697 394585390869746875968523)
      ·
        refine ⟨591878086304620313952785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394585390869746875968523 591878086304620313952785)
        ·
          refine ⟨443908564728465235464589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591878086304620313952785 443908564728465235464589)
          ·
            refine ⟨166465711773174463299221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443908564728465235464589 166465711773174463299221)
            ·
              refine ⟨7803080239367552967151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166465711773174463299221 7803080239367552967151)
              ·
                rfl

theorem cell19_76932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_76932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76932 prefixEnd_76932 := by exact prefixLift 76932
  have htrace : WordTrace (prefixWord ++ tailWord_76932) baseStart_76932 baseEnd_76932 := by
    simpa [prefixWord, tailWord_76932, baseEnd_76932] using wordTrace_append hprefix tailTrace_76932
  have hstable : (prefixWord ++ tailWord_76932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76932).length < 2 ^ (prefixWord ++ tailWord_76932).sum := by decide
  have hdescent : baseEnd_76932 < baseStart_76932 := by decide
  rcases family_descends (prefixWord ++ tailWord_76932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76991 : List Nat := [1, 1, 2, 2, 2, 2, 9]
def baseStart_76991 : Nat := 118140960795 + 76991 * 2 ^ 59
def prefixEnd_76991 : Nat := 4983230072969 + 3 ^ 40 * 76991 * 2
def baseEnd_76991 : Nat := 7809064507736001196727

theorem tailTrace_76991 : CollatzResearch.WordTrace tailWord_76991 prefixEnd_76991 7809064507736001196727 := by
  unfold tailWord_76991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808092464082230861062827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1872061642721487240708551 2808092464082230861062827)
  ·
    refine ⟨4212138696123346291594241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2808092464082230861062827 4212138696123346291594241)
    ·
      refine ⟨3159104022092509718695681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4212138696123346291594241 3159104022092509718695681)
      ·
        refine ⟨2369328016569382289021761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3159104022092509718695681 2369328016569382289021761)
        ·
          refine ⟨1776996012427036716766321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369328016569382289021761 1776996012427036716766321)
          ·
            refine ⟨1332747009320277537574741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776996012427036716766321 1332747009320277537574741)
            ·
              refine ⟨7809064507736001196727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1332747009320277537574741 7809064507736001196727)
              ·
                rfl

theorem cell19_76991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_76991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_76991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_76991 prefixEnd_76991 := by exact prefixLift 76991
  have htrace : WordTrace (prefixWord ++ tailWord_76991) baseStart_76991 baseEnd_76991 := by
    simpa [prefixWord, tailWord_76991, baseEnd_76991] using wordTrace_append hprefix tailTrace_76991
  have hstable : (prefixWord ++ tailWord_76991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76991).length < 2 ^ (prefixWord ++ tailWord_76991).sum := by decide
  have hdescent : baseEnd_76991 < baseStart_76991 := by decide
  rcases family_descends (prefixWord ++ tailWord_76991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77006 : List Nat := [4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_77006 : Nat := 118140960795 + 77006 * 2 ^ 59
def prefixEnd_77006 : Nat := 4983230072969 + 3 ^ 40 * 77006 * 2
def baseEnd_77006 : Nat := 23431757795692413256807

theorem tailTrace_77006 : CollatzResearch.WordTrace tailWord_77006 prefixEnd_77006 23431757795692413256807 := by
  unfold tailWord_77006
  simp only [CollatzResearch.WordTrace]
  refine ⟨351079944878486052857359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1872426372685258948572581 351079944878486052857359)
  ·
    refine ⟨526619917317729079286039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351079944878486052857359 526619917317729079286039)
    ·
      refine ⟨789929875976593618929059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526619917317729079286039 789929875976593618929059)
      ·
        refine ⟨1184894813964890428393589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789929875976593618929059 1184894813964890428393589)
        ·
          refine ⟨111083888809208477661899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1184894813964890428393589 111083888809208477661899)
          ·
            refine ⟨166625833213812716492849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111083888809208477661899 166625833213812716492849)
            ·
              refine ⟨124969374910359537369637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166625833213812716492849 124969374910359537369637)
              ·
                refine ⟨23431757795692413256807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124969374910359537369637 23431757795692413256807)
                ·
                  rfl

theorem cell19_77006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_77006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77006 prefixEnd_77006 := by exact prefixLift 77006
  have htrace : WordTrace (prefixWord ++ tailWord_77006) baseStart_77006 baseEnd_77006 := by
    simpa [prefixWord, tailWord_77006, baseEnd_77006] using wordTrace_append hprefix tailTrace_77006
  have hstable : (prefixWord ++ tailWord_77006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77006).length < 2 ^ (prefixWord ++ tailWord_77006).sum := by decide
  have hdescent : baseEnd_77006 < baseStart_77006 := by decide
  rcases family_descends (prefixWord ++ tailWord_77006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77082 : List Nat := [3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_77082 : Nat := 118140960795 + 77082 * 2 ^ 59
def prefixEnd_77082 : Nat := 4983230072969 + 3 ^ 40 * 77082 * 2
def baseEnd_77082 : Nat := 23454883442946755567711

theorem tailTrace_77082 : CollatzResearch.WordTrace tailWord_77082 prefixEnd_77082 23454883442946755567711 := by
  unfold tailWord_77082
  simp only [CollatzResearch.WordTrace]
  refine ⟨702852876688138350656375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1874274337835035601750333 702852876688138350656375)
  ·
    refine ⟨1054279315032207525984563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702852876688138350656375 1054279315032207525984563)
    ·
      refine ⟨1581418972548311288976845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054279315032207525984563 1581418972548311288976845)
      ·
        refine ⟨593032114705616733366317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1581418972548311288976845 593032114705616733366317)
        ·
          refine ⟨222387043014606275012369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593032114705616733366317 222387043014606275012369)
          ·
            refine ⟨166790282260954706259277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222387043014606275012369 166790282260954706259277)
            ·
              refine ⟨62546355847858014847229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166790282260954706259277 62546355847858014847229)
              ·
                refine ⟨23454883442946755567711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62546355847858014847229 23454883442946755567711)
                ·
                  rfl

theorem cell19_77082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_77082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77082 prefixEnd_77082 := by exact prefixLift 77082
  have htrace : WordTrace (prefixWord ++ tailWord_77082) baseStart_77082 baseEnd_77082 := by
    simpa [prefixWord, tailWord_77082, baseEnd_77082] using wordTrace_append hprefix tailTrace_77082
  have hstable : (prefixWord ++ tailWord_77082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77082).length < 2 ^ (prefixWord ++ tailWord_77082).sum := by decide
  have hdescent : baseEnd_77082 < baseStart_77082 := by decide
  rcases family_descends (prefixWord ++ tailWord_77082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77101 : List Nat := [1, 5, 3, 1, 1, 2, 6]
def baseStart_77101 : Nat := 118140960795 + 77101 * 2 ^ 59
def prefixEnd_77101 : Nat := 4983230072969 + 3 ^ 40 * 77101 * 2
def baseEnd_77101 : Nat := 7820221618253447048479

theorem tailTrace_77101 : CollatzResearch.WordTrace tailWord_77101 prefixEnd_77101 7820221618253447048479 := by
  unfold tailWord_77101
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812104493683719647567157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1874736329122479765044771 2812104493683719647567157)
  ·
    refine ⟨263634796282848716959421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2812104493683719647567157 263634796282848716959421)
    ·
      refine ⟨98863048606068268859783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263634796282848716959421 98863048606068268859783)
      ·
        refine ⟨148294572909102403289675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98863048606068268859783 148294572909102403289675)
        ·
          refine ⟨222441859363653604934513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148294572909102403289675 222441859363653604934513)
          ·
            refine ⟨166831394522740203700885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222441859363653604934513 166831394522740203700885)
            ·
              refine ⟨7820221618253447048479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166831394522740203700885 7820221618253447048479)
              ·
                rfl

theorem cell19_77101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_77101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77101 prefixEnd_77101 := by exact prefixLift 77101
  have htrace : WordTrace (prefixWord ++ tailWord_77101) baseStart_77101 baseEnd_77101 := by
    simpa [prefixWord, tailWord_77101, baseEnd_77101] using wordTrace_append hprefix tailTrace_77101
  have hstable : (prefixWord ++ tailWord_77101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77101).length < 2 ^ (prefixWord ++ tailWord_77101).sum := by decide
  have hdescent : baseEnd_77101 < baseStart_77101 := by decide
  rcases family_descends (prefixWord ++ tailWord_77101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77133 : List Nat := [1, 6, 1, 3, 2, 1, 2, 3]
def baseStart_77133 : Nat := 118140960795 + 77133 * 2 ^ 59
def prefixEnd_77133 : Nat := 4983230072969 + 3 ^ 40 * 77133 * 2
def baseEnd_77133 : Nat := 23470401969393748434239

theorem tailTrace_77133 : CollatzResearch.WordTrace tailWord_77133 prefixEnd_77133 23470401969393748434239 := by
  unfold tailWord_77133
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813271629567789112732053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1875514419711859408488035 2813271629567789112732053)
  ·
    refine ⟨131872107635990114659315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2813271629567789112732053 131872107635990114659315)
    ·
      refine ⟨197808161453985171988973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131872107635990114659315 197808161453985171988973)
      ·
        refine ⟨74178060545244439495865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197808161453985171988973 74178060545244439495865)
        ·
          refine ⟨55633545408933329621899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74178060545244439495865 55633545408933329621899)
          ·
            refine ⟨83450318113399994432849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55633545408933329621899 83450318113399994432849)
            ·
              refine ⟨62587738585049995824637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83450318113399994432849 62587738585049995824637)
              ·
                refine ⟨23470401969393748434239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62587738585049995824637 23470401969393748434239)
                ·
                  rfl

theorem cell19_77133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_77133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77133 prefixEnd_77133 := by exact prefixLift 77133
  have htrace : WordTrace (prefixWord ++ tailWord_77133) baseStart_77133 baseEnd_77133 := by
    simpa [prefixWord, tailWord_77133, baseEnd_77133] using wordTrace_append hprefix tailTrace_77133
  have hstable : (prefixWord ++ tailWord_77133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77133).length < 2 ^ (prefixWord ++ tailWord_77133).sum := by decide
  have hdescent : baseEnd_77133 < baseStart_77133 := by decide
  rcases family_descends (prefixWord ++ tailWord_77133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77141 : List Nat := [1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_77141 : Nat := 118140960795 + 77141 * 2 ^ 59
def prefixEnd_77141 : Nat := 4983230072969 + 3 ^ 40 * 77141 * 2
def baseEnd_77141 : Nat := 23472836248052100256439

theorem tailTrace_77141 : CollatzResearch.WordTrace tailWord_77141 prefixEnd_77141 23472836248052100256439 := by
  unfold tailWord_77141
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813563413538806479023277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1875708942359204319348851 2813563413538806479023277)
  ·
    refine ⟨1055086280077052429633729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2813563413538806479023277 1055086280077052429633729)
    ·
      refine ⟨791314710057789322225297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1055086280077052429633729 791314710057789322225297)
      ·
        refine ⟨593486032543341991668973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 791314710057789322225297 593486032543341991668973)
        ·
          refine ⟨222557262203753246875865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593486032543341991668973 222557262203753246875865)
          ·
            refine ⟨166917946652814935156899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222557262203753246875865 166917946652814935156899)
            ·
              refine ⟨250376919979222402735349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166917946652814935156899 250376919979222402735349)
              ·
                refine ⟨23472836248052100256439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250376919979222402735349 23472836248052100256439)
                ·
                  rfl

theorem cell19_77141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_77141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77141 prefixEnd_77141 := by exact prefixLift 77141
  have htrace : WordTrace (prefixWord ++ tailWord_77141) baseStart_77141 baseEnd_77141 := by
    simpa [prefixWord, tailWord_77141, baseEnd_77141] using wordTrace_append hprefix tailTrace_77141
  have hstable : (prefixWord ++ tailWord_77141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77141).length < 2 ^ (prefixWord ++ tailWord_77141).sum := by decide
  have hdescent : baseEnd_77141 < baseStart_77141 := by decide
  rcases family_descends (prefixWord ++ tailWord_77141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77255 : List Nat := [1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_77255 : Nat := 118140960795 + 77255 * 2 ^ 59
def prefixEnd_77255 : Nat := 4983230072969 + 3 ^ 40 * 77255 * 2
def baseEnd_77255 : Nat := 23507524718933613722795

theorem tailTrace_77255 : CollatzResearch.WordTrace tailWord_77255 prefixEnd_77255 23507524718933613722795 := by
  unfold tailWord_77255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817721335125803948673219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1878480890083869299115479 2817721335125803948673219)
  ·
    refine ⟨4226582002688705923009829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2817721335125803948673219 4226582002688705923009829)
    ·
      refine ⟨792484125504132360564343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4226582002688705923009829 792484125504132360564343)
      ·
        refine ⟨1188726188256198540846515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792484125504132360564343 1188726188256198540846515)
        ·
          refine ⟨1783089282384297811269773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188726188256198540846515 1783089282384297811269773)
          ·
            refine ⟨668658480894111679226165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1783089282384297811269773 668658480894111679226165)
            ·
              refine ⟨62686732583822969927453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 668658480894111679226165 62686732583822969927453)
              ·
                refine ⟨23507524718933613722795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62686732583822969927453 23507524718933613722795)
                ·
                  rfl

theorem cell19_77255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_77255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77255 prefixEnd_77255 := by exact prefixLift 77255
  have htrace : WordTrace (prefixWord ++ tailWord_77255) baseStart_77255 baseEnd_77255 := by
    simpa [prefixWord, tailWord_77255, baseEnd_77255] using wordTrace_append hprefix tailTrace_77255
  have hstable : (prefixWord ++ tailWord_77255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77255).length < 2 ^ (prefixWord ++ tailWord_77255).sum := by decide
  have hdescent : baseEnd_77255 < baseStart_77255 := by decide
  rcases family_descends (prefixWord ++ tailWord_77255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77325 : List Nat := [1, 7, 1, 1, 3, 1, 5]
def baseStart_77325 : Nat := 118140960795 + 77325 * 2 ^ 59
def prefixEnd_77325 : Nat := 4983230072969 + 3 ^ 40 * 77325 * 2
def baseEnd_77325 : Nat := 7842941552398064055683

theorem tailTrace_77325 : CollatzResearch.WordTrace tailWord_77325 prefixEnd_77325 7842941552398064055683 := by
  unfold tailWord_77325
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820274444872205903721429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1880182963248137269147619 2820274444872205903721429)
  ·
    refine ⟨66100182301692325868471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2820274444872205903721429 66100182301692325868471)
    ·
      refine ⟨99150273452538488802707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66100182301692325868471 99150273452538488802707)
      ·
        refine ⟨148725410178807733204061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99150273452538488802707 148725410178807733204061)
        ·
          refine ⟨55772028817052899951523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148725410178807733204061 55772028817052899951523)
          ·
            refine ⟨83658043225579349927285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55772028817052899951523 83658043225579349927285)
            ·
              refine ⟨7842941552398064055683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83658043225579349927285 7842941552398064055683)
              ·
                rfl

theorem cell19_77325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_77325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77325 prefixEnd_77325 := by exact prefixLift 77325
  have htrace : WordTrace (prefixWord ++ tailWord_77325) baseStart_77325 baseEnd_77325 := by
    simpa [prefixWord, tailWord_77325, baseEnd_77325] using wordTrace_append hprefix tailTrace_77325
  have hstable : (prefixWord ++ tailWord_77325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77325).length < 2 ^ (prefixWord ++ tailWord_77325).sum := by decide
  have hdescent : baseEnd_77325 < baseStart_77325 := by decide
  rcases family_descends (prefixWord ++ tailWord_77325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77333 : List Nat := [1, 3, 2, 1, 3, 2, 7]
def baseStart_77333 : Nat := 118140960795 + 77333 * 2 ^ 59
def prefixEnd_77333 : Nat := 4983230072969 + 3 ^ 40 * 77333 * 2
def baseEnd_77333 : Nat := 7843752978617514663083

theorem tailTrace_77333 : CollatzResearch.WordTrace tailWord_77333 prefixEnd_77333 7843752978617514663083 := by
  unfold tailWord_77333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820566228843223270012653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1880377485895482180008435 2820566228843223270012653)
  ·
    refine ⟨1057712335816208726254745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2820566228843223270012653 1057712335816208726254745)
    ·
      refine ⟨793284251862156544691059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057712335816208726254745 793284251862156544691059)
      ·
        refine ⟨1189926377793234817036589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793284251862156544691059 1189926377793234817036589)
        ·
          refine ⟨446222391672463056388721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1189926377793234817036589 446222391672463056388721)
          ·
            refine ⟨334666793754347292291541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446222391672463056388721 334666793754347292291541)
            ·
              refine ⟨7843752978617514663083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 334666793754347292291541 7843752978617514663083)
              ·
                rfl

theorem cell19_77333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_77333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77333 prefixEnd_77333 := by exact prefixLift 77333
  have htrace : WordTrace (prefixWord ++ tailWord_77333) baseStart_77333 baseEnd_77333 := by
    simpa [prefixWord, tailWord_77333, baseEnd_77333] using wordTrace_append hprefix tailTrace_77333
  have hstable : (prefixWord ++ tailWord_77333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77333).length < 2 ^ (prefixWord ++ tailWord_77333).sum := by decide
  have hdescent : baseEnd_77333 < baseStart_77333 := by decide
  rcases family_descends (prefixWord ++ tailWord_77333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77447 : List Nat := [1, 1, 4, 2, 1, 4, 6]
def baseStart_77447 : Nat := 118140960795 + 77447 * 2 ^ 59
def prefixEnd_77447 : Nat := 4983230072969 + 3 ^ 40 * 77447 * 2
def baseEnd_77447 : Nat := 7855315802244685818535

theorem tailTrace_77447 : CollatzResearch.WordTrace tailWord_77447 prefixEnd_77447 7855315802244685818535 := by
  unfold tailWord_77447
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824724150430220739662595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1883149433620147159775063 2824724150430220739662595)
  ·
    refine ⟨4237086225645331109493893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824724150430220739662595 4237086225645331109493893)
    ·
      refine ⟨794453667308499583030105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4237086225645331109493893 794453667308499583030105)
      ·
        refine ⟨595840250481374687272579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794453667308499583030105 595840250481374687272579)
        ·
          refine ⟨893760375722062030908869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595840250481374687272579 893760375722062030908869)
          ·
            refine ⟨167580070447886630795413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 893760375722062030908869 167580070447886630795413)
            ·
              refine ⟨7855315802244685818535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167580070447886630795413 7855315802244685818535)
              ·
                rfl

theorem cell19_77447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_77447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77447 prefixEnd_77447 := by exact prefixLift 77447
  have htrace : WordTrace (prefixWord ++ tailWord_77447) baseStart_77447 baseEnd_77447 := by
    simpa [prefixWord, tailWord_77447, baseEnd_77447] using wordTrace_append hprefix tailTrace_77447
  have hstable : (prefixWord ++ tailWord_77447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77447).length < 2 ^ (prefixWord ++ tailWord_77447).sum := by decide
  have hdescent : baseEnd_77447 < baseStart_77447 := by decide
  rcases family_descends (prefixWord ++ tailWord_77447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77502 : List Nat := [4, 2, 1, 1, 2, 4, 5]
def baseStart_77502 : Nat := 118140960795 + 77502 * 2 ^ 59
def prefixEnd_77502 : Nat := 4983230072969 + 3 ^ 40 * 77502 * 2
def baseEnd_77502 : Nat := 7860894357503408744411

theorem tailTrace_77502 : CollatzResearch.WordTrace tailWord_77502 prefixEnd_77502 7860894357503408744411 := by
  unfold tailWord_77502
  simp only [CollatzResearch.WordTrace]
  refine ⟨353341270653870641614345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1884486776820643421943173 353341270653870641614345)
  ·
    refine ⟨265005952990402981210759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 353341270653870641614345 265005952990402981210759)
    ·
      refine ⟨397508929485604471816139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265005952990402981210759 397508929485604471816139)
      ·
        refine ⟨596263394228406707724209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397508929485604471816139 596263394228406707724209)
        ·
          refine ⟨447197545671305030793157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596263394228406707724209 447197545671305030793157)
          ·
            refine ⟨83849539813369693273717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 447197545671305030793157 83849539813369693273717)
            ·
              refine ⟨7860894357503408744411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83849539813369693273717 7860894357503408744411)
              ·
                rfl

theorem cell19_77502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_77502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77502 prefixEnd_77502 := by exact prefixLift 77502
  have htrace : WordTrace (prefixWord ++ tailWord_77502) baseStart_77502 baseEnd_77502 := by
    simpa [prefixWord, tailWord_77502, baseEnd_77502] using wordTrace_append hprefix tailTrace_77502
  have hstable : (prefixWord ++ tailWord_77502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77502).length < 2 ^ (prefixWord ++ tailWord_77502).sum := by decide
  have hdescent : baseEnd_77502 < baseStart_77502 := by decide
  rcases family_descends (prefixWord ++ tailWord_77502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77578 : List Nat := [3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_77578 : Nat := 118140960795 + 77578 * 2 ^ 59
def prefixEnd_77578 : Nat := 4983230072969 + 3 ^ 40 * 77578 * 2
def baseEnd_77578 : Nat := 23605808719764568544137

theorem tailTrace_77578 : CollatzResearch.WordTrace tailWord_77578 prefixEnd_77578 23605808719764568544137 := by
  unfold tailWord_77578
  simp only [CollatzResearch.WordTrace]
  refine ⟨707375528238907528170347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1886334741970420075120925 707375528238907528170347)
  ·
    refine ⟨1061063292358361292255521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 707375528238907528170347 1061063292358361292255521)
    ·
      refine ⟨795797469268770969191641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1061063292358361292255521 795797469268770969191641)
      ·
        refine ⟨596848101951578226893731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 795797469268770969191641 596848101951578226893731)
        ·
          refine ⟨895272152927367340340597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596848101951578226893731 895272152927367340340597)
          ·
            refine ⟨83931764336940688156931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 895272152927367340340597 83931764336940688156931)
            ·
              refine ⟨125897646505411032235397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83931764336940688156931 125897646505411032235397)
              ·
                refine ⟨23605808719764568544137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125897646505411032235397 23605808719764568544137)
                ·
                  rfl

theorem cell19_77578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_77578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77578 prefixEnd_77578 := by exact prefixLift 77578
  have htrace : WordTrace (prefixWord ++ tailWord_77578) baseStart_77578 baseEnd_77578 := by
    simpa [prefixWord, tailWord_77578, baseEnd_77578] using wordTrace_append hprefix tailTrace_77578
  have hstable : (prefixWord ++ tailWord_77578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77578).length < 2 ^ (prefixWord ++ tailWord_77578).sum := by decide
  have hdescent : baseEnd_77578 < baseStart_77578 := by decide
  rcases family_descends (prefixWord ++ tailWord_77578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77580 : List Nat := [2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_77580 : Nat := 118140960795 + 77580 * 2 ^ 59
def prefixEnd_77580 : Nat := 4983230072969 + 3 ^ 40 * 77580 * 2
def baseEnd_77580 : Nat := 23606417289429156499687

theorem tailTrace_77580 : CollatzResearch.WordTrace tailWord_77580 prefixEnd_77580 23606417289429156499687 := by
  unfold tailWord_77580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414787529474192227127097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1886383372632256302836129 1414787529474192227127097)
  ·
    refine ⟨1061090647105644170345323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1414787529474192227127097 1061090647105644170345323)
    ·
      refine ⟨1591635970658466255517985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061090647105644170345323 1591635970658466255517985)
      ·
        refine ⟨1193726977993849691638489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1591635970658466255517985 1193726977993849691638489)
        ·
          refine ⟨895295233495387268728867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193726977993849691638489 895295233495387268728867)
          ·
            refine ⟨1342942850243080903093301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895295233495387268728867 1342942850243080903093301)
            ·
              refine ⟨125900892210288834664997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1342942850243080903093301 125900892210288834664997)
              ·
                refine ⟨23606417289429156499687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125900892210288834664997 23606417289429156499687)
                ·
                  rfl

theorem cell19_77580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_77580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77580 prefixEnd_77580 := by exact prefixLift 77580
  have htrace : WordTrace (prefixWord ++ tailWord_77580) baseStart_77580 baseEnd_77580 := by
    simpa [prefixWord, tailWord_77580, baseEnd_77580] using wordTrace_append hprefix tailTrace_77580
  have hstable : (prefixWord ++ tailWord_77580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77580).length < 2 ^ (prefixWord ++ tailWord_77580).sum := by decide
  have hdescent : baseEnd_77580 < baseStart_77580 := by decide
  rcases family_descends (prefixWord ++ tailWord_77580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77618 : List Nat := [3, 2, 1, 1, 3, 3, 6]
def baseStart_77618 : Nat := 118140960795 + 77618 * 2 ^ 59
def prefixEnd_77618 : Nat := 4983230072969 + 3 ^ 40 * 77618 * 2
def baseEnd_77618 : Nat := 7872660037685442551713

theorem tailTrace_77618 : CollatzResearch.WordTrace tailWord_77618 prefixEnd_77618 7872660037685442551713 := by
  unfold tailWord_77618
  simp only [CollatzResearch.WordTrace]
  refine ⟨707740258202679236034377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1887307355207144629425005 707740258202679236034377)
  ·
    refine ⟨530805193652009427025783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 707740258202679236034377 530805193652009427025783)
    ·
      refine ⟨796207790478014140538675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530805193652009427025783 796207790478014140538675)
      ·
        refine ⟨1194311685717021210808013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796207790478014140538675 1194311685717021210808013)
        ·
          refine ⟨447866882143882954053005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1194311685717021210808013 447866882143882954053005)
          ·
            refine ⟨167950080803956107769877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447866882143882954053005 167950080803956107769877)
            ·
              refine ⟨7872660037685442551713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167950080803956107769877 7872660037685442551713)
              ·
                rfl

theorem cell19_77618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_77618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77618 prefixEnd_77618 := by exact prefixLift 77618
  have htrace : WordTrace (prefixWord ++ tailWord_77618) baseStart_77618 baseEnd_77618 := by
    simpa [prefixWord, tailWord_77618, baseEnd_77618] using wordTrace_append hprefix tailTrace_77618
  have hstable : (prefixWord ++ tailWord_77618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77618).length < 2 ^ (prefixWord ++ tailWord_77618).sum := by decide
  have hdescent : baseEnd_77618 < baseStart_77618 := by decide
  rcases family_descends (prefixWord ++ tailWord_77618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77652 : List Nat := [2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_77652 : Nat := 118140960795 + 77652 * 2 ^ 59
def prefixEnd_77652 : Nat := 4983230072969 + 3 ^ 40 * 77652 * 2
def baseEnd_77652 : Nat := 23628325797354322899491

theorem tailTrace_77652 : CollatzResearch.WordTrace tailWord_77652 prefixEnd_77652 23628325797354322899491 := by
  unfold tailWord_77652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416100557343770375437605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1888134076458360500583473 1416100557343770375437605)
  ·
    refine ⟨265518854501956945394551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1416100557343770375437605 265518854501956945394551)
    ·
      refine ⟨398278281752935418091827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265518854501956945394551 398278281752935418091827)
      ·
        refine ⟨597417422629403127137741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398278281752935418091827 597417422629403127137741)
        ·
          refine ⟨224031533486026172676653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 597417422629403127137741 224031533486026172676653)
          ·
            refine ⟨84011825057259814753745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224031533486026172676653 84011825057259814753745)
            ·
              refine ⟨63008868792944861065309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84011825057259814753745 63008868792944861065309)
              ·
                refine ⟨23628325797354322899491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63008868792944861065309 23628325797354322899491)
                ·
                  rfl

theorem cell19_77652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_77652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77652 prefixEnd_77652 := by exact prefixLift 77652
  have htrace : WordTrace (prefixWord ++ tailWord_77652) baseStart_77652 baseEnd_77652 := by
    simpa [prefixWord, tailWord_77652, baseEnd_77652] using wordTrace_append hprefix tailTrace_77652
  have hstable : (prefixWord ++ tailWord_77652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77652).length < 2 ^ (prefixWord ++ tailWord_77652).sum := by decide
  have hdescent : baseEnd_77652 < baseStart_77652 := by decide
  rcases family_descends (prefixWord ++ tailWord_77652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77730 : List Nat := [3, 3, 1, 2, 4, 6]
def baseStart_77730 : Nat := 118140960795 + 77730 * 2 ^ 59
def prefixEnd_77730 : Nat := 4983230072969 + 3 ^ 40 * 77730 * 2
def baseEnd_77730 : Nat := 2628006668252583685105

theorem tailTrace_77730 : CollatzResearch.WordTrace tailWord_77730 prefixEnd_77730 2628006668252583685105 := by
  unfold tailWord_77730
  simp only [CollatzResearch.WordTrace]
  refine ⟨708761502101240018053661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1890030672269973381476429 708761502101240018053661)
  ·
    refine ⟨265785563287965006770123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 708761502101240018053661 265785563287965006770123)
    ·
      refine ⟨398678344931947510155185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265785563287965006770123 398678344931947510155185)
      ·
        refine ⟨299008758698960632616389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398678344931947510155185 299008758698960632616389)
        ·
          refine ⟨56064142256055118615573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299008758698960632616389 56064142256055118615573)
          ·
            refine ⟨2628006668252583685105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56064142256055118615573 2628006668252583685105)
            ·
              rfl

theorem cell19_77730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_77730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77730 prefixEnd_77730 := by exact prefixLift 77730
  have htrace : WordTrace (prefixWord ++ tailWord_77730) baseStart_77730 baseEnd_77730 := by
    simpa [prefixWord, tailWord_77730, baseEnd_77730] using wordTrace_append hprefix tailTrace_77730
  have hstable : (prefixWord ++ tailWord_77730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77730).length < 2 ^ (prefixWord ++ tailWord_77730).sum := by decide
  have hdescent : baseEnd_77730 < baseStart_77730 := by decide
  rcases family_descends (prefixWord ++ tailWord_77730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77749 : List Nat := [1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_77749 : Nat := 118140960795 + 77749 * 2 ^ 59
def prefixEnd_77749 : Nat := 4983230072969 + 3 ^ 40 * 77749 * 2
def baseEnd_77749 : Nat := 23657841426086838743671

theorem tailTrace_77749 : CollatzResearch.WordTrace tailWord_77749 prefixEnd_77749 23657841426086838743671 := by
  unfold tailWord_77749
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835738995336126317156301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1890492663557417544770867 2835738995336126317156301)
  ·
    refine ⟨1063402123251047368933613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2835738995336126317156301 1063402123251047368933613)
    ·
      refine ⟨398775796219142763350105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1063402123251047368933613 398775796219142763350105)
      ·
        refine ⟨299081847164357072512579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398775796219142763350105 299081847164357072512579)
        ·
          refine ⟨448622770746535608768869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299081847164357072512579 448622770746535608768869)
          ·
            refine ⟨84116769514975426644163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 448622770746535608768869 84116769514975426644163)
            ·
              refine ⟨126175154272463139966245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84116769514975426644163 126175154272463139966245)
              ·
                refine ⟨23657841426086838743671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126175154272463139966245 23657841426086838743671)
                ·
                  rfl

theorem cell19_77749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_77749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77749 prefixEnd_77749 := by exact prefixLift 77749
  have htrace : WordTrace (prefixWord ++ tailWord_77749) baseStart_77749 baseEnd_77749 := by
    simpa [prefixWord, tailWord_77749, baseEnd_77749] using wordTrace_append hprefix tailTrace_77749
  have hstable : (prefixWord ++ tailWord_77749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77749).length < 2 ^ (prefixWord ++ tailWord_77749).sum := by decide
  have hdescent : baseEnd_77749 < baseStart_77749 := by decide
  rcases family_descends (prefixWord ++ tailWord_77749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77768 : List Nat := [2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_77768 : Nat := 118140960795 + 77768 * 2 ^ 59
def prefixEnd_77768 : Nat := 4983230072969 + 3 ^ 40 * 77768 * 2
def baseEnd_77768 : Nat := 23663622837900424321397

theorem tailTrace_77768 : CollatzResearch.WordTrace tailWord_77768 prefixEnd_77768 23663622837900424321397 := by
  unfold tailWord_77768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418215991133646281048979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1890954654844861708065305 1418215991133646281048979)
  ·
    refine ⟨2127323986700469421573469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418215991133646281048979 2127323986700469421573469)
    ·
      refine ⟨797746495012676033090051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2127323986700469421573469 797746495012676033090051)
      ·
        refine ⟨1196619742519014049635077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797746495012676033090051 1196619742519014049635077)
        ·
          refine ⟨224366201722315134306577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1196619742519014049635077 224366201722315134306577)
          ·
            refine ⟨168274651291736350729933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224366201722315134306577 168274651291736350729933)
            ·
              refine ⟨63102994234401131523725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168274651291736350729933 63102994234401131523725)
              ·
                refine ⟨23663622837900424321397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63102994234401131523725 23663622837900424321397)
                ·
                  rfl

theorem cell19_77768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_77768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77768 prefixEnd_77768 := by exact prefixLift 77768
  have htrace : WordTrace (prefixWord ++ tailWord_77768) baseStart_77768 baseEnd_77768 := by
    simpa [prefixWord, tailWord_77768, baseEnd_77768] using wordTrace_append hprefix tailTrace_77768
  have hstable : (prefixWord ++ tailWord_77768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77768).length < 2 ^ (prefixWord ++ tailWord_77768).sum := by decide
  have hdescent : baseEnd_77768 < baseStart_77768 := by decide
  rcases family_descends (prefixWord ++ tailWord_77768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77960 : List Nat := [2, 1, 3, 4, 1, 2, 6]
def baseStart_77960 : Nat := 118140960795 + 77960 * 2 ^ 59
def prefixEnd_77960 : Nat := 4983230072969 + 3 ^ 40 * 77960 * 2
def baseEnd_77960 : Nat := 7907348508566956018069

theorem tailTrace_77960 : CollatzResearch.WordTrace tailWord_77960 prefixEnd_77960 7907348508566956018069 := by
  unfold tailWord_77960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421717398785854676543667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1895623198381139568724889 1421717398785854676543667)
  ·
    refine ⟨2132576098178782014815501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421717398785854676543667 2132576098178782014815501)
    ·
      refine ⟨799716036817043255555813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2132576098178782014815501 799716036817043255555813)
      ·
        refine ⟨149946756903195610416715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 799716036817043255555813 149946756903195610416715)
        ·
          refine ⟨224920135354793415625073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149946756903195610416715 224920135354793415625073)
          ·
            refine ⟨168690101516095061718805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224920135354793415625073 168690101516095061718805)
            ·
              refine ⟨7907348508566956018069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168690101516095061718805 7907348508566956018069)
              ·
                rfl

theorem cell19_77960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_77960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_77960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_77960 prefixEnd_77960 := by exact prefixLift 77960
  have htrace : WordTrace (prefixWord ++ tailWord_77960) baseStart_77960 baseEnd_77960 := by
    simpa [prefixWord, tailWord_77960, baseEnd_77960] using wordTrace_append hprefix tailTrace_77960
  have hstable : (prefixWord ++ tailWord_77960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77960).length < 2 ^ (prefixWord ++ tailWord_77960).sum := by decide
  have hdescent : baseEnd_77960 < baseStart_77960 := by decide
  rcases family_descends (prefixWord ++ tailWord_77960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78055 : List Nat := [1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_78055 : Nat := 118140960795 + 78055 * 2 ^ 59
def prefixEnd_78055 : Nat := 4983230072969 + 3 ^ 40 * 78055 * 2
def baseEnd_78055 : Nat := 23750952584768795942837

theorem tailTrace_78055 : CollatzResearch.WordTrace tailWord_78055 prefixEnd_78055 23750952584768795942837 := by
  unfold tailWord_78055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846899732227540577795619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1897933154818360385197079 2846899732227540577795619)
  ·
    refine ⟨4270349598341310866693429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2846899732227540577795619 4270349598341310866693429)
    ·
      refine ⟨400345274844497893752509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4270349598341310866693429 400345274844497893752509)
      ·
        refine ⟨150129478066686710157191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400345274844497893752509 150129478066686710157191)
        ·
          refine ⟨225194217100030065235787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150129478066686710157191 225194217100030065235787)
          ·
            refine ⟨337791325650045097853681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225194217100030065235787 337791325650045097853681)
            ·
              refine ⟨253343494237533823390261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337791325650045097853681 253343494237533823390261)
              ·
                refine ⟨23750952584768795942837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253343494237533823390261 23750952584768795942837)
                ·
                  rfl

theorem cell19_78055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_78055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78055 prefixEnd_78055 := by exact prefixLift 78055
  have htrace : WordTrace (prefixWord ++ tailWord_78055) baseStart_78055 baseEnd_78055 := by
    simpa [prefixWord, tailWord_78055, baseEnd_78055] using wordTrace_append hprefix tailTrace_78055
  have hstable : (prefixWord ++ tailWord_78055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78055).length < 2 ^ (prefixWord ++ tailWord_78055).sum := by decide
  have hdescent : baseEnd_78055 < baseStart_78055 := by decide
  rcases family_descends (prefixWord ++ tailWord_78055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78076 : List Nat := [2, 2, 2, 1, 4, 8]
def baseStart_78076 : Nat := 118140960795 + 78076 * 2 ^ 59
def prefixEnd_78076 : Nat := 4983230072969 + 3 ^ 40 * 78076 * 2
def baseEnd_78076 : Nat := 2639704729582996608457

theorem tailTrace_78076 : CollatzResearch.WordTrace tailWord_78076 prefixEnd_78076 2639704729582996608457 := by
  unfold tailWord_78076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423832832575730582155041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1898443776767640776206721 1423832832575730582155041)
  ·
    refine ⟨1067874624431797936616281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1423832832575730582155041 1067874624431797936616281)
    ·
      refine ⟨800905968323848452462211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1067874624431797936616281 800905968323848452462211)
      ·
        refine ⟨1201358952485772678693317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800905968323848452462211 1201358952485772678693317)
        ·
          refine ⟨225254803591082377254997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1201358952485772678693317 225254803591082377254997)
          ·
            refine ⟨2639704729582996608457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 225254803591082377254997 2639704729582996608457)
            ·
              rfl

theorem cell19_78076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_78076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78076 prefixEnd_78076 := by exact prefixLift 78076
  have htrace : WordTrace (prefixWord ++ tailWord_78076) baseStart_78076 baseEnd_78076 := by
    simpa [prefixWord, tailWord_78076, baseEnd_78076] using wordTrace_append hprefix tailTrace_78076
  have hstable : (prefixWord ++ tailWord_78076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78076).length < 2 ^ (prefixWord ++ tailWord_78076).sum := by decide
  have hdescent : baseEnd_78076 < baseStart_78076 := by decide
  rcases family_descends (prefixWord ++ tailWord_78076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78133 : List Nat := [1, 3, 3, 1, 2, 1, 8]
def baseStart_78133 : Nat := 118140960795 + 78133 * 2 ^ 59
def prefixEnd_78133 : Nat := 4983230072969 + 3 ^ 40 * 78133 * 2
def baseEnd_78133 : Nat := 7924895600562575403097

theorem tailTrace_78133 : CollatzResearch.WordTrace tailWord_78133 prefixEnd_78133 7924895600562575403097 := by
  unfold tailWord_78133
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849744625944959899135053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1899829750629973266090035 2849744625944959899135053)
  ·
    refine ⟨1068654234729359962175645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2849744625944959899135053 1068654234729359962175645)
    ·
      refine ⟨400745338023509985815867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1068654234729359962175645 400745338023509985815867)
      ·
        refine ⟨601118007035264978723801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400745338023509985815867 601118007035264978723801)
        ·
          refine ⟨450838505276448734042851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601118007035264978723801 450838505276448734042851)
          ·
            refine ⟨676257757914673101064277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450838505276448734042851 676257757914673101064277)
            ·
              refine ⟨7924895600562575403097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 676257757914673101064277 7924895600562575403097)
              ·
                rfl

theorem cell19_78133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_78133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78133 prefixEnd_78133 := by exact prefixLift 78133
  have htrace : WordTrace (prefixWord ++ tailWord_78133) baseStart_78133 baseEnd_78133 := by
    simpa [prefixWord, tailWord_78133, baseEnd_78133] using wordTrace_append hprefix tailTrace_78133
  have hstable : (prefixWord ++ tailWord_78133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78133).length < 2 ^ (prefixWord ++ tailWord_78133).sum := by decide
  have hdescent : baseEnd_78133 < baseStart_78133 := by decide
  rcases family_descends (prefixWord ++ tailWord_78133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78165 : List Nat := [1, 3, 2, 2, 5, 1, 2, 3]
def baseStart_78165 : Nat := 118140960795 + 78165 * 2 ^ 59
def prefixEnd_78165 : Nat := 4983230072969 + 3 ^ 40 * 78165 * 2
def baseEnd_78165 : Nat := 23784423916321133498093

theorem tailTrace_78165 : CollatzResearch.WordTrace tailWord_78165 prefixEnd_78165 23784423916321133498093 := by
  unfold tailWord_78165
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850911761829029364299949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1900607841219352909533299 2850911761829029364299949)
  ·
    refine ⟨1069091910685886011612481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2850911761829029364299949 1069091910685886011612481)
    ·
      refine ⟨801818933014414508709361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1069091910685886011612481 801818933014414508709361)
      ·
        refine ⟨601364199760810881532021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801818933014414508709361 601364199760810881532021)
        ·
          refine ⟨56377893727576020143627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 601364199760810881532021 56377893727576020143627)
          ·
            refine ⟨84566840591364030215441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56377893727576020143627 84566840591364030215441)
            ·
              refine ⟨63425130443523022661581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84566840591364030215441 63425130443523022661581)
              ·
                refine ⟨23784423916321133498093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63425130443523022661581 23784423916321133498093)
                ·
                  rfl

theorem cell19_78165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_78165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78165 prefixEnd_78165 := by exact prefixLift 78165
  have htrace : WordTrace (prefixWord ++ tailWord_78165) baseStart_78165 baseEnd_78165 := by
    simpa [prefixWord, tailWord_78165, baseEnd_78165] using wordTrace_append hprefix tailTrace_78165
  have hstable : (prefixWord ++ tailWord_78165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78165).length < 2 ^ (prefixWord ++ tailWord_78165).sum := by decide
  have hdescent : baseEnd_78165 < baseStart_78165 := by decide
  rcases family_descends (prefixWord ++ tailWord_78165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78188 : List Nat := [2, 2, 1, 1, 6, 2, 5]
def baseStart_78188 : Nat := 118140960795 + 78188 * 2 ^ 59
def prefixEnd_78188 : Nat := 4983230072969 + 3 ^ 40 * 78188 * 2
def baseEnd_78188 : Nat := 7930474155821298328973

theorem tailTrace_78188 : CollatzResearch.WordTrace tailWord_78188 prefixEnd_78188 7930474155821298328973 := by
  unfold tailWord_78188
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425875320372852146193609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1901167093830469528258145 1425875320372852146193609)
  ·
    refine ⟨1069406490279639109645207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1425875320372852146193609 1069406490279639109645207)
    ·
      refine ⟨1604109735419458664467811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069406490279639109645207 1604109735419458664467811)
      ·
        refine ⟨2406164603129187996701717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604109735419458664467811 2406164603129187996701717)
        ·
          refine ⟨112788965771680687345393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2406164603129187996701717 112788965771680687345393)
          ·
            refine ⟨84591724328760515509045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112788965771680687345393 84591724328760515509045)
            ·
              refine ⟨7930474155821298328973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84591724328760515509045 7930474155821298328973)
              ·
                rfl

theorem cell19_78188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_78188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78188 prefixEnd_78188 := by exact prefixLift 78188
  have htrace : WordTrace (prefixWord ++ tailWord_78188) baseStart_78188 baseEnd_78188 := by
    simpa [prefixWord, tailWord_78188, baseEnd_78188] using wordTrace_append hprefix tailTrace_78188
  have hstable : (prefixWord ++ tailWord_78188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78188).length < 2 ^ (prefixWord ++ tailWord_78188).sum := by decide
  have hdescent : baseEnd_78188 < baseStart_78188 := by decide
  rcases family_descends (prefixWord ++ tailWord_78188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78247 : List Nat := [1, 1, 6, 1, 1, 9]
def baseStart_78247 : Nat := 118140960795 + 78247 * 2 ^ 59
def prefixEnd_78247 : Nat := 4983230072969 + 3 ^ 40 * 78247 * 2
def baseEnd_78247 : Nat := 2645486141396582186183

theorem tailTrace_78247 : CollatzResearch.WordTrace tailWord_78247 prefixEnd_78247 2645486141396582186183 := by
  unfold tailWord_78247
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853902547531957368784995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1902601698354638245856663 2853902547531957368784995)
  ·
    refine ⟨4280853821297936053177493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853902547531957368784995 4280853821297936053177493)
    ·
      refine ⟨200665022873340752492695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4280853821297936053177493 200665022873340752492695)
      ·
        refine ⟨300997534310011128739043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200665022873340752492695 300997534310011128739043)
        ·
          refine ⟨451496301465016693108565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300997534310011128739043 451496301465016693108565)
          ·
            refine ⟨2645486141396582186183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 451496301465016693108565 2645486141396582186183)
            ·
              rfl

theorem cell19_78247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_78247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78247 prefixEnd_78247 := by exact prefixLift 78247
  have htrace : WordTrace (prefixWord ++ tailWord_78247) baseStart_78247 baseEnd_78247 := by
    simpa [prefixWord, tailWord_78247, baseEnd_78247] using wordTrace_append hprefix tailTrace_78247
  have hstable : (prefixWord ++ tailWord_78247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78247).length < 2 ^ (prefixWord ++ tailWord_78247).sum := by decide
  have hdescent : baseEnd_78247 < baseStart_78247 := by decide
  rcases family_descends (prefixWord ++ tailWord_78247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78338 : List Nat := [3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_78338 : Nat := 118140960795 + 78338 * 2 ^ 59
def prefixEnd_78338 : Nat := 4983230072969 + 3 ^ 40 * 78338 * 2
def baseEnd_78338 : Nat := 23837065192307991653177

theorem tailTrace_78338 : CollatzResearch.WordTrace tailWord_78338 prefixEnd_78338 23837065192307991653177 := by
  unfold tailWord_78338
  simp only [CollatzResearch.WordTrace]
  refine ⟨714305397550569977586917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1904814393468186606898445 714305397550569977586917)
  ·
    refine ⟨133932262040731870797547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 714305397550569977586917 133932262040731870797547)
    ·
      refine ⟨200898393061097806196321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133932262040731870797547 200898393061097806196321)
      ·
        refine ⟨150673794795823354647241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200898393061097806196321 150673794795823354647241)
        ·
          refine ⟨113005346096867515985431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150673794795823354647241 113005346096867515985431)
          ·
            refine ⟨169508019145301273978147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113005346096867515985431 169508019145301273978147)
            ·
              refine ⟨254262028717951910967221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169508019145301273978147 254262028717951910967221)
              ·
                refine ⟨23837065192307991653177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254262028717951910967221 23837065192307991653177)
                ·
                  rfl

theorem cell19_78338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_78338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78338 prefixEnd_78338 := by exact prefixLift 78338
  have htrace : WordTrace (prefixWord ++ tailWord_78338) baseStart_78338 baseEnd_78338 := by
    simpa [prefixWord, tailWord_78338, baseEnd_78338] using wordTrace_append hprefix tailTrace_78338
  have hstable : (prefixWord ++ tailWord_78338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78338).length < 2 ^ (prefixWord ++ tailWord_78338).sum := by decide
  have hdescent : baseEnd_78338 < baseStart_78338 := by decide
  rcases family_descends (prefixWord ++ tailWord_78338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78340 : List Nat := [2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_78340 : Nat := 118140960795 + 78340 * 2 ^ 59
def prefixEnd_78340 : Nat := 4983230072969 + 3 ^ 40 * 78340 * 2
def baseEnd_78340 : Nat := 23837673761972579608727

theorem tailTrace_78340 : CollatzResearch.WordTrace tailWord_78340 prefixEnd_78340 23837673761972579608727 := by
  unfold tailWord_78340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428647268097517125960237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1904863024130022834613649 1428647268097517125960237)
  ·
    refine ⟨535742725536568922235089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1428647268097517125960237 535742725536568922235089)
    ·
      refine ⟨401807044152426691676317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 535742725536568922235089 401807044152426691676317)
      ·
        refine ⟨150677641557160009378619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401807044152426691676317 150677641557160009378619)
        ·
          refine ⟨226016462335740014067929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150677641557160009378619 226016462335740014067929)
          ·
            refine ⟨169512346751805010550947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226016462335740014067929 169512346751805010550947)
            ·
              refine ⟨254268520127707515826421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169512346751805010550947 254268520127707515826421)
              ·
                refine ⟨23837673761972579608727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254268520127707515826421 23837673761972579608727)
                ·
                  rfl

theorem cell19_78340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_78340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78340 prefixEnd_78340 := by exact prefixLift 78340
  have htrace : WordTrace (prefixWord ++ tailWord_78340) baseStart_78340 baseEnd_78340 := by
    simpa [prefixWord, tailWord_78340, baseEnd_78340] using wordTrace_append hprefix tailTrace_78340
  have hstable : (prefixWord ++ tailWord_78340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78340).length < 2 ^ (prefixWord ++ tailWord_78340).sum := by decide
  have hdescent : baseEnd_78340 < baseStart_78340 := by decide
  rcases family_descends (prefixWord ++ tailWord_78340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78378 : List Nat := [3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_78378 : Nat := 118140960795 + 78378 * 2 ^ 59
def prefixEnd_78378 : Nat := 4983230072969 + 3 ^ 40 * 78378 * 2
def baseEnd_78378 : Nat := 23849236585599750764179

theorem tailTrace_78378 : CollatzResearch.WordTrace tailWord_78378 prefixEnd_78378 23849236585599750764179 := by
  unfold tailWord_78378
  simp only [CollatzResearch.WordTrace]
  refine ⟨714670127514341685450947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1905787006704911161202525 714670127514341685450947)
  ·
    refine ⟨1072005191271512528176421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714670127514341685450947 1072005191271512528176421)
    ·
      refine ⟨201000973363408599033079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1072005191271512528176421 201000973363408599033079)
      ·
        refine ⟨301501460045112898549619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201000973363408599033079 301501460045112898549619)
        ·
          refine ⟨452252190067669347824429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301501460045112898549619 452252190067669347824429)
          ·
            refine ⟨169594571275376005434161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 452252190067669347824429 169594571275376005434161)
            ·
              refine ⟨127195928456532004075621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169594571275376005434161 127195928456532004075621)
              ·
                refine ⟨23849236585599750764179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127195928456532004075621 23849236585599750764179)
                ·
                  rfl

theorem cell19_78378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_78378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78378 prefixEnd_78378 := by exact prefixLift 78378
  have htrace : WordTrace (prefixWord ++ tailWord_78378) baseStart_78378 baseEnd_78378 := by
    simpa [prefixWord, tailWord_78378, baseEnd_78378] using wordTrace_append hprefix tailTrace_78378
  have hstable : (prefixWord ++ tailWord_78378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78378).length < 2 ^ (prefixWord ++ tailWord_78378).sum := by decide
  have hdescent : baseEnd_78378 < baseStart_78378 := by decide
  rcases family_descends (prefixWord ++ tailWord_78378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78509 : List Nat := [1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_78509 : Nat := 118140960795 + 78509 * 2 ^ 59
def prefixEnd_78509 : Nat := 4983230072969 + 3 ^ 40 * 78509 * 2
def baseEnd_78509 : Nat := 23889097898630261852711

theorem tailTrace_78509 : CollatzResearch.WordTrace tailWord_78509 prefixEnd_78509 23889097898630261852711 := by
  unfold tailWord_78509
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863458472582776114822581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1908972315055184076548387 2863458472582776114822581)
  ·
    refine ⟨268449231804635260764617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2863458472582776114822581 268449231804635260764617)
    ·
      refine ⟨201336923853476445573463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268449231804635260764617 201336923853476445573463)
      ·
        refine ⟨302005385780214668360195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201336923853476445573463 302005385780214668360195)
        ·
          refine ⟨453008078670322002540293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302005385780214668360195 453008078670322002540293)
          ·
            refine ⟨84939014750685375476305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 453008078670322002540293 84939014750685375476305)
            ·
              refine ⟨63704261063014031607229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84939014750685375476305 63704261063014031607229)
              ·
                refine ⟨23889097898630261852711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63704261063014031607229 23889097898630261852711)
                ·
                  rfl

theorem cell19_78509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_78509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78509 prefixEnd_78509 := by exact prefixLift 78509
  have htrace : WordTrace (prefixWord ++ tailWord_78509) baseStart_78509 baseEnd_78509 := by
    simpa [prefixWord, tailWord_78509, baseEnd_78509] using wordTrace_append hprefix tailTrace_78509
  have hstable : (prefixWord ++ tailWord_78509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78509).length < 2 ^ (prefixWord ++ tailWord_78509).sum := by decide
  have hdescent : baseEnd_78509 < baseStart_78509 := by decide
  rcases family_descends (prefixWord ++ tailWord_78509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78511 : List Nat := [1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_78511 : Nat := 118140960795 + 78511 * 2 ^ 59
def prefixEnd_78511 : Nat := 4983230072969 + 3 ^ 40 * 78511 * 2
def baseEnd_78511 : Nat := 23889706468294849808261

theorem tailTrace_78511 : CollatzResearch.WordTrace tailWord_78511 prefixEnd_78511 23889706468294849808261 := by
  unfold tailWord_78511
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863531418575530456395387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1909020945717020304263591 2863531418575530456395387)
  ·
    refine ⟨4295297127863295684593081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2863531418575530456395387 4295297127863295684593081)
    ·
      refine ⟨3221472845897471763444811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4295297127863295684593081 3221472845897471763444811)
      ·
        refine ⟨4832209268846207645167217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221472845897471763444811 4832209268846207645167217)
        ·
          refine ⟨3624156951634655733875413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4832209268846207645167217 3624156951634655733875413)
          ·
            refine ⟨84941178553937243762705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3624156951634655733875413 84941178553937243762705)
            ·
              refine ⟨63705883915452932822029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84941178553937243762705 63705883915452932822029)
              ·
                refine ⟨23889706468294849808261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63705883915452932822029 23889706468294849808261)
                ·
                  rfl

theorem cell19_78511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_78511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78511 prefixEnd_78511 := by exact prefixLift 78511
  have htrace : WordTrace (prefixWord ++ tailWord_78511) baseStart_78511 baseEnd_78511 := by
    simpa [prefixWord, tailWord_78511, baseEnd_78511] using wordTrace_append hprefix tailTrace_78511
  have hstable : (prefixWord ++ tailWord_78511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78511).length < 2 ^ (prefixWord ++ tailWord_78511).sum := by decide
  have hdescent : baseEnd_78511 < baseStart_78511 := by decide
  rcases family_descends (prefixWord ++ tailWord_78511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78532 : List Nat := [2, 3, 3, 1, 1, 2, 7]
def baseStart_78532 : Nat := 118140960795 + 78532 * 2 ^ 59
def prefixEnd_78532 : Nat := 4983230072969 + 3 ^ 40 * 78532 * 2
def baseEnd_78532 : Nat := 7965365483257674447179

theorem tailTrace_78532 : CollatzResearch.WordTrace tailWord_78532 prefixEnd_78532 7965365483257674447179 := by
  unfold tailWord_78532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432148675749725521454925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1909531567666300695273233 1432148675749725521454925)
  ·
    refine ⟨537055753406147070545597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1432148675749725521454925 537055753406147070545597)
    ·
      refine ⟨201395907527305151454599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 537055753406147070545597 201395907527305151454599)
      ·
        refine ⟨302093861290957727181899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201395907527305151454599 302093861290957727181899)
        ·
          refine ⟨453140791936436590772849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302093861290957727181899 453140791936436590772849)
          ·
            refine ⟨339855593952327443079637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453140791936436590772849 339855593952327443079637)
            ·
              refine ⟨7965365483257674447179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 339855593952327443079637 7965365483257674447179)
              ·
                rfl

theorem cell19_78532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_78532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78532 prefixEnd_78532 := by exact prefixLift 78532
  have htrace : WordTrace (prefixWord ++ tailWord_78532) baseStart_78532 baseEnd_78532 := by
    simpa [prefixWord, tailWord_78532, baseEnd_78532] using wordTrace_append hprefix tailTrace_78532
  have hstable : (prefixWord ++ tailWord_78532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78532).length < 2 ^ (prefixWord ++ tailWord_78532).sum := by decide
  have hdescent : baseEnd_78532 < baseStart_78532 := by decide
  rcases family_descends (prefixWord ++ tailWord_78532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78551 : List Nat := [1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_78551 : Nat := 118140960795 + 78551 * 2 ^ 59
def prefixEnd_78551 : Nat := 4983230072969 + 3 ^ 40 * 78551 * 2
def baseEnd_78551 : Nat := 23901877861586608919263

theorem tailTrace_78551 : CollatzResearch.WordTrace tailWord_78551 prefixEnd_78551 23901877861586608919263 := by
  unfold tailWord_78551
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864990338430617287851507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1909993558953744858567671 2864990338430617287851507)
  ·
    refine ⟨4297485507645925931777261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2864990338430617287851507 4297485507645925931777261)
    ·
      refine ⟨1611557065367222224416473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4297485507645925931777261 1611557065367222224416473)
      ·
        refine ⟨1208667799025416668312355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611557065367222224416473 1208667799025416668312355)
        ·
          refine ⟨1813001698538125002468533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208667799025416668312355 1813001698538125002468533)
          ·
            refine ⟨169968909237949218981425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1813001698538125002468533 169968909237949218981425)
            ·
              refine ⟨127476681928461914236069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169968909237949218981425 127476681928461914236069)
              ·
                refine ⟨23901877861586608919263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127476681928461914236069 23901877861586608919263)
                ·
                  rfl

theorem cell19_78551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_78551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78551 prefixEnd_78551 := by exact prefixLift 78551
  have htrace : WordTrace (prefixWord ++ tailWord_78551) baseStart_78551 baseEnd_78551 := by
    simpa [prefixWord, tailWord_78551, baseEnd_78551] using wordTrace_append hprefix tailTrace_78551
  have hstable : (prefixWord ++ tailWord_78551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78551).length < 2 ^ (prefixWord ++ tailWord_78551).sum := by decide
  have hdescent : baseEnd_78551 < baseStart_78551 := by decide
  rcases family_descends (prefixWord ++ tailWord_78551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78644 : List Nat := [2, 5, 1, 1, 3, 1, 6]
def baseStart_78644 : Nat := 118140960795 + 78644 * 2 ^ 59
def prefixEnd_78644 : Nat := 4983230072969 + 3 ^ 40 * 78644 * 2
def baseEnd_78644 : Nat := 7976725450329982950781

theorem tailTrace_78644 : CollatzResearch.WordTrace tailWord_78644 prefixEnd_78644 7976725450329982950781 := by
  unfold tailWord_78644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434191163546847085493493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1912254884729129447324657 1434191163546847085493493)
  ·
    refine ⟨134455421582516914265015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1434191163546847085493493 134455421582516914265015)
    ·
      refine ⟨201683132373775371397523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134455421582516914265015 201683132373775371397523)
      ·
        refine ⟨302524698560663057096285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201683132373775371397523 302524698560663057096285)
        ·
          refine ⟨113446761960248646411107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302524698560663057096285 113446761960248646411107)
          ·
            refine ⟨170170142940372969616661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113446761960248646411107 170170142940372969616661)
            ·
              refine ⟨7976725450329982950781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170170142940372969616661 7976725450329982950781)
              ·
                rfl

theorem cell19_78644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_78644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78644 prefixEnd_78644 := by exact prefixLift 78644
  have htrace : WordTrace (prefixWord ++ tailWord_78644) baseStart_78644 baseEnd_78644 := by
    simpa [prefixWord, tailWord_78644, baseEnd_78644] using wordTrace_append hprefix tailTrace_78644
  have hstable : (prefixWord ++ tailWord_78644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78644).length < 2 ^ (prefixWord ++ tailWord_78644).sum := by decide
  have hdescent : baseEnd_78644 < baseStart_78644 := by decide
  rcases family_descends (prefixWord ++ tailWord_78644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78648 : List Nat := [2, 1, 2, 1, 3, 2, 8]
def baseStart_78648 : Nat := 118140960795 + 78648 * 2 ^ 59
def prefixEnd_78648 : Nat := 4983230072969 + 3 ^ 40 * 78648 * 2
def baseEnd_78648 : Nat := 7977131163439708254481

theorem tailTrace_78648 : CollatzResearch.WordTrace tailWord_78648 prefixEnd_78648 7977131163439708254481 := by
  unfold tailWord_78648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434264109539601427066299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1912352146052801902755065 1434264109539601427066299)
  ·
    refine ⟨2151396164309402140599449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434264109539601427066299 2151396164309402140599449)
    ·
      refine ⟨1613547123232051605449587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2151396164309402140599449 1613547123232051605449587)
      ·
        refine ⟨2420320684848077408174381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613547123232051605449587 2420320684848077408174381)
        ·
          refine ⟨907620256818029028065393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2420320684848077408174381 907620256818029028065393)
          ·
            refine ⟨680715192613521771049045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907620256818029028065393 680715192613521771049045)
            ·
              refine ⟨7977131163439708254481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 680715192613521771049045 7977131163439708254481)
              ·
                rfl

theorem cell19_78648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_78648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78648 prefixEnd_78648 := by exact prefixLift 78648
  have htrace : WordTrace (prefixWord ++ tailWord_78648) baseStart_78648 baseEnd_78648 := by
    simpa [prefixWord, tailWord_78648, baseEnd_78648] using wordTrace_append hprefix tailTrace_78648
  have hstable : (prefixWord ++ tailWord_78648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78648).length < 2 ^ (prefixWord ++ tailWord_78648).sum := by decide
  have hdescent : baseEnd_78648 < baseStart_78648 := by decide
  rcases family_descends (prefixWord ++ tailWord_78648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78682 : List Nat := [3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_78682 : Nat := 118140960795 + 78682 * 2 ^ 59
def prefixEnd_78682 : Nat := 4983230072969 + 3 ^ 40 * 78682 * 2
def baseEnd_78682 : Nat := 23941739174617120007795

theorem tailTrace_78682 : CollatzResearch.WordTrace tailWord_78682 prefixEnd_78682 23941739174617120007795 := by
  unfold tailWord_78682
  simp only [CollatzResearch.WordTrace]
  refine ⟨717442075239006665217575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1913178867304017773913533 717442075239006665217575)
  ·
    refine ⟨1076163112858509997826363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717442075239006665217575 1076163112858509997826363)
    ·
      refine ⟨1614244669287764996739545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076163112858509997826363 1614244669287764996739545)
      ·
        refine ⟨1210683501965823747554659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614244669287764996739545 1210683501965823747554659)
        ·
          refine ⟨1816025252948735621331989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210683501965823747554659 1816025252948735621331989)
          ·
            refine ⟨85126183731971982249937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1816025252948735621331989 85126183731971982249937)
            ·
              refine ⟨63844637798978986687453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85126183731971982249937 63844637798978986687453)
              ·
                refine ⟨23941739174617120007795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63844637798978986687453 23941739174617120007795)
                ·
                  rfl

theorem cell19_78682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_78682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78682 prefixEnd_78682 := by exact prefixLift 78682
  have htrace : WordTrace (prefixWord ++ tailWord_78682) baseStart_78682 baseEnd_78682 := by
    simpa [prefixWord, tailWord_78682, baseEnd_78682] using wordTrace_append hprefix tailTrace_78682
  have hstable : (prefixWord ++ tailWord_78682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78682).length < 2 ^ (prefixWord ++ tailWord_78682).sum := by decide
  have hdescent : baseEnd_78682 < baseStart_78682 := by decide
  rcases family_descends (prefixWord ++ tailWord_78682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78705 : List Nat := [1, 2, 2, 2, 1, 4, 7]
def baseStart_78705 : Nat := 118140960795 + 78705 * 2 ^ 59
def prefixEnd_78705 : Nat := 4983230072969 + 3 ^ 40 * 78705 * 2
def baseEnd_78705 : Nat := 7982912575253293832207

theorem tailTrace_78705 : CollatzResearch.WordTrace tailWord_78705 prefixEnd_78705 7982912575253293832207 := by
  unfold tailWord_78705
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870607179872701588957569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1913738119915134392638379 2870607179872701588957569)
  ·
    refine ⟨2152955384904526191718177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2870607179872701588957569 2152955384904526191718177)
    ·
      refine ⟨1614716538678394643788633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2152955384904526191718177 1614716538678394643788633)
      ·
        refine ⟨1211037404008795982841475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614716538678394643788633 1211037404008795982841475)
        ·
          refine ⟨1816556106013193974262213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211037404008795982841475 1816556106013193974262213)
          ·
            refine ⟨340604269877473870174165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1816556106013193974262213 340604269877473870174165)
            ·
              refine ⟨7982912575253293832207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 340604269877473870174165 7982912575253293832207)
              ·
                rfl

theorem cell19_78705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_78705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78705 prefixEnd_78705 := by exact prefixLift 78705
  have htrace : WordTrace (prefixWord ++ tailWord_78705) baseStart_78705 baseEnd_78705 := by
    simpa [prefixWord, tailWord_78705, baseEnd_78705] using wordTrace_append hprefix tailTrace_78705
  have hstable : (prefixWord ++ tailWord_78705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78705).length < 2 ^ (prefixWord ++ tailWord_78705).sum := by decide
  have hdescent : baseEnd_78705 < baseStart_78705 := by decide
  rcases family_descends (prefixWord ++ tailWord_78705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78718 : List Nat := [4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_78718 : Nat := 118140960795 + 78718 * 2 ^ 59
def prefixEnd_78718 : Nat := 4983230072969 + 3 ^ 40 * 78718 * 2
def baseEnd_78718 : Nat := 23952693428579703207697

theorem tailTrace_78718 : CollatzResearch.WordTrace tailWord_78718 prefixEnd_78718 23952693428579703207697 := by
  unfold tailWord_78718
  simp only [CollatzResearch.WordTrace]
  refine ⟨358885166103200601147601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1914054219217069872787205 358885166103200601147601)
  ·
    refine ⟨269163874577400450860701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 358885166103200601147601 269163874577400450860701)
    ·
      refine ⟨100936452966525169072763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269163874577400450860701 100936452966525169072763)
      ·
        refine ⟨151404679449787753609145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100936452966525169072763 151404679449787753609145)
        ·
          refine ⟨113553509587340815206859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151404679449787753609145 113553509587340815206859)
          ·
            refine ⟨170330264381011222810289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113553509587340815206859 170330264381011222810289)
            ·
              refine ⟨127747698285758417107717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170330264381011222810289 127747698285758417107717)
              ·
                refine ⟨23952693428579703207697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127747698285758417107717 23952693428579703207697)
                ·
                  rfl

theorem cell19_78718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_78718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78718 prefixEnd_78718 := by exact prefixLift 78718
  have htrace : WordTrace (prefixWord ++ tailWord_78718) baseStart_78718 baseEnd_78718 := by
    simpa [prefixWord, tailWord_78718, baseEnd_78718] using wordTrace_append hprefix tailTrace_78718
  have hstable : (prefixWord ++ tailWord_78718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78718).length < 2 ^ (prefixWord ++ tailWord_78718).sum := by decide
  have hdescent : baseEnd_78718 < baseStart_78718 := by decide
  rcases family_descends (prefixWord ++ tailWord_78718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78743 : List Nat := [1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_78743 : Nat := 118140960795 + 78743 * 2 ^ 59
def prefixEnd_78743 : Nat := 4983230072969 + 3 ^ 40 * 78743 * 2
def baseEnd_78743 : Nat := 23960300549387052652073

theorem tailTrace_78743 : CollatzResearch.WordTrace tailWord_78743 prefixEnd_78743 23960300549387052652073 := by
  unfold tailWord_78743
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871993153735034078840883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1914662102490022719227255 2871993153735034078840883)
  ·
    refine ⟨4307989730602551118261325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2871993153735034078840883 4307989730602551118261325)
    ·
      refine ⟨1615496148975956669347997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4307989730602551118261325 1615496148975956669347997)
      ·
        refine ⟨605811055865983751005499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1615496148975956669347997 605811055865983751005499)
        ·
          refine ⟨908716583798975626508249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605811055865983751005499 908716583798975626508249)
          ·
            refine ⟨681537437849231719881187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 908716583798975626508249 681537437849231719881187)
            ·
              refine ⟨1022306156773847579821781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681537437849231719881187 1022306156773847579821781)
              ·
                refine ⟨23960300549387052652073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1022306156773847579821781 23960300549387052652073)
                ·
                  rfl

theorem cell19_78743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_78743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78743 prefixEnd_78743 := by exact prefixLift 78743
  have htrace : WordTrace (prefixWord ++ tailWord_78743) baseStart_78743 baseEnd_78743 := by
    simpa [prefixWord, tailWord_78743, baseEnd_78743] using wordTrace_append hprefix tailTrace_78743
  have hstable : (prefixWord ++ tailWord_78743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78743).length < 2 ^ (prefixWord ++ tailWord_78743).sum := by decide
  have hdescent : baseEnd_78743 < baseStart_78743 := by decide
  rcases family_descends (prefixWord ++ tailWord_78743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78819 : List Nat := [1, 1, 1, 6, 1, 1, 8]
def baseStart_78819 : Nat := 118140960795 + 78819 * 2 ^ 59
def prefixEnd_78819 : Nat := 4983230072969 + 3 ^ 40 * 78819 * 2
def baseEnd_78819 : Nat := 7994475398880464987659

theorem tailTrace_78819 : CollatzResearch.WordTrace tailWord_78819 prefixEnd_78819 7994475398880464987659 := by
  unfold tailWord_78819
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874765101459699058607511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1916510067639799372405007 2874765101459699058607511)
  ·
    refine ⟨4312147652189548587911267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874765101459699058607511 4312147652189548587911267)
    ·
      refine ⟨6468221478284322881866901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4312147652189548587911267 6468221478284322881866901)
      ·
        refine ⟨303197881794577635087511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6468221478284322881866901 303197881794577635087511)
        ·
          refine ⟨454796822691866452631267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303197881794577635087511 454796822691866452631267)
          ·
            refine ⟨682195234037799678946901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454796822691866452631267 682195234037799678946901)
            ·
              refine ⟨7994475398880464987659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 682195234037799678946901 7994475398880464987659)
              ·
                rfl

theorem cell19_78819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_78819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78819 prefixEnd_78819 := by exact prefixLift 78819
  have htrace : WordTrace (prefixWord ++ tailWord_78819) baseStart_78819 baseEnd_78819 := by
    simpa [prefixWord, tailWord_78819, baseEnd_78819] using wordTrace_append hprefix tailTrace_78819
  have hstable : (prefixWord ++ tailWord_78819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78819).length < 2 ^ (prefixWord ++ tailWord_78819).sum := by decide
  have hdescent : baseEnd_78819 < baseStart_78819 := by decide
  rcases family_descends (prefixWord ++ tailWord_78819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78965 : List Nat := [1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_78965 : Nat := 118140960795 + 78965 * 2 ^ 59
def prefixEnd_78965 : Nat := 4983230072969 + 3 ^ 40 * 78965 * 2
def baseEnd_78965 : Nat := 24027851782156315718135

theorem tailTrace_78965 : CollatzResearch.WordTrace tailWord_78965 prefixEnd_78965 24027851782156315718135 := by
  unfold tailWord_78965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880090158930765993422349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1920060105953843995614899 2880090158930765993422349)
  ·
    refine ⟨1080033809599037247533381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2880090158930765993422349 1080033809599037247533381)
    ·
      refine ⟨202506339299819483912509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1080033809599037247533381 202506339299819483912509)
      ·
        refine ⟨75939877237432306467191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202506339299819483912509 75939877237432306467191)
        ·
          refine ⟨113909815856148459700787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75939877237432306467191 113909815856148459700787)
          ·
            refine ⟨170864723784222689551181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113909815856148459700787 170864723784222689551181)
            ·
              refine ⟨64074271419083508581693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170864723784222689551181 64074271419083508581693)
              ·
                refine ⟨24027851782156315718135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64074271419083508581693 24027851782156315718135)
                ·
                  rfl

theorem cell19_78965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_78965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_78965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_78965 prefixEnd_78965 := by exact prefixLift 78965
  have htrace : WordTrace (prefixWord ++ tailWord_78965) baseStart_78965 baseEnd_78965 := by
    simpa [prefixWord, tailWord_78965, baseEnd_78965] using wordTrace_append hprefix tailTrace_78965
  have hstable : (prefixWord ++ tailWord_78965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78965).length < 2 ^ (prefixWord ++ tailWord_78965).sum := by decide
  have hdescent : baseEnd_78965 < baseStart_78965 := by decide
  rcases family_descends (prefixWord ++ tailWord_78965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79009 : List Nat := [1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_79009 : Nat := 118140960795 + 79009 * 2 ^ 59
def prefixEnd_79009 : Nat := 4983230072969 + 3 ^ 40 * 79009 * 2
def baseEnd_79009 : Nat := 24041240314777250740237

theorem tailTrace_79009 : CollatzResearch.WordTrace tailWord_79009 prefixEnd_79009 24041240314777250740237 := by
  unfold tailWord_79009
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881694970771361508024081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1921129980514241005349387 2881694970771361508024081)
  ·
    refine ⟨2161271228078521131018061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2881694970771361508024081 2161271228078521131018061)
    ·
      refine ⟨810476710529445424131773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2161271228078521131018061 810476710529445424131773)
      ·
        refine ⟨303928766448542034049415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 810476710529445424131773 303928766448542034049415)
        ·
          refine ⟨455893149672813051074123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303928766448542034049415 455893149672813051074123)
          ·
            refine ⟨683839724509219576611185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455893149672813051074123 683839724509219576611185)
            ·
              refine ⟨512879793381914682458389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683839724509219576611185 512879793381914682458389)
              ·
                refine ⟨24041240314777250740237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 512879793381914682458389 24041240314777250740237)
                ·
                  rfl

theorem cell19_79009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_79009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79009 prefixEnd_79009 := by exact prefixLift 79009
  have htrace : WordTrace (prefixWord ++ tailWord_79009) baseStart_79009 baseEnd_79009 := by
    simpa [prefixWord, tailWord_79009, baseEnd_79009] using wordTrace_append hprefix tailTrace_79009
  have hstable : (prefixWord ++ tailWord_79009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79009).length < 2 ^ (prefixWord ++ tailWord_79009).sum := by decide
  have hdescent : baseEnd_79009 < baseStart_79009 := by decide
  rcases family_descends (prefixWord ++ tailWord_79009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79026 : List Nat := [3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_79026 : Nat := 118140960795 + 79026 * 2 ^ 59
def prefixEnd_79026 : Nat := 4983230072969 + 3 ^ 40 * 79026 * 2
def baseEnd_79026 : Nat := 24046413156926248362413

theorem tailTrace_79026 : CollatzResearch.WordTrace tailWord_79026 prefixEnd_79026 24046413156926248362413 := by
  unfold tailWord_79026
  simp only [CollatzResearch.WordTrace]
  refine ⟨720578752927443352848233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1921543341139848940928621 720578752927443352848233)
  ·
    refine ⟨540434064695582514636175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 720578752927443352848233 540434064695582514636175)
    ·
      refine ⟨810651097043373771954263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540434064695582514636175 810651097043373771954263)
      ·
        refine ⟨1215976645565060657931395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810651097043373771954263 1215976645565060657931395)
        ·
          refine ⟨1823964968347590986897093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215976645565060657931395 1823964968347590986897093)
          ·
            refine ⟨341993431565173310043205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1823964968347590986897093 341993431565173310043205)
            ·
              refine ⟨64123768418469995633101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 341993431565173310043205 64123768418469995633101)
              ·
                refine ⟨24046413156926248362413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64123768418469995633101 24046413156926248362413)
                ·
                  rfl

theorem cell19_79026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_79026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79026 prefixEnd_79026 := by exact prefixLift 79026
  have htrace : WordTrace (prefixWord ++ tailWord_79026) baseStart_79026 baseEnd_79026 := by
    simpa [prefixWord, tailWord_79026, baseEnd_79026] using wordTrace_append hprefix tailTrace_79026
  have hstable : (prefixWord ++ tailWord_79026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79026).length < 2 ^ (prefixWord ++ tailWord_79026).sum := by decide
  have hdescent : baseEnd_79026 < baseStart_79026 := by decide
  rcases family_descends (prefixWord ++ tailWord_79026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79064 : List Nat := [2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_79064 : Nat := 118140960795 + 79064 * 2 ^ 59
def prefixEnd_79064 : Nat := 4983230072969 + 3 ^ 40 * 79064 * 2
def baseEnd_79064 : Nat := 24057975980553419517865

theorem tailTrace_79064 : CollatzResearch.WordTrace tailWord_79064 prefixEnd_79064 24057975980553419517865 := by
  unfold tailWord_79064
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441850492786052950638123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1922467323714737267517497 1441850492786052950638123)
  ·
    refine ⟨2162775739179079425957185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441850492786052950638123 2162775739179079425957185)
    ·
      refine ⟨1622081804384309569467889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2162775739179079425957185 1622081804384309569467889)
      ·
        refine ⟨1216561353288232177100917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1622081804384309569467889 1216561353288232177100917)
        ·
          refine ⟨114052626870771766603211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1216561353288232177100917 114052626870771766603211)
          ·
            refine ⟨171078940306157649904817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114052626870771766603211 171078940306157649904817)
            ·
              refine ⟨128309205229618237428613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171078940306157649904817 128309205229618237428613)
              ·
                refine ⟨24057975980553419517865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128309205229618237428613 24057975980553419517865)
                ·
                  rfl

theorem cell19_79064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_79064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79064 prefixEnd_79064 := by exact prefixLift 79064
  have htrace : WordTrace (prefixWord ++ tailWord_79064) baseStart_79064 baseEnd_79064 := by
    simpa [prefixWord, tailWord_79064, baseEnd_79064] using wordTrace_append hprefix tailTrace_79064
  have hstable : (prefixWord ++ tailWord_79064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79064).length < 2 ^ (prefixWord ++ tailWord_79064).sum := by decide
  have hdescent : baseEnd_79064 < baseStart_79064 := by decide
  rcases family_descends (prefixWord ++ tailWord_79064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79138 : List Nat := [3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_79138 : Nat := 118140960795 + 79138 * 2 ^ 59
def prefixEnd_79138 : Nat := 4983230072969 + 3 ^ 40 * 79138 * 2
def baseEnd_79138 : Nat := 24080493058143173873219

theorem tailTrace_79138 : CollatzResearch.WordTrace tailWord_79138 prefixEnd_79138 24080493058143173873219 := by
  unfold tailWord_79138
  simp only [CollatzResearch.WordTrace]
  refine ⟨721599996826004134867517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1924266658202677692980045 721599996826004134867517)
  ·
    refine ⟨270599998809751550575319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 721599996826004134867517 270599998809751550575319)
    ·
      refine ⟨405899998214627325862979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270599998809751550575319 405899998214627325862979)
      ·
        refine ⟨608849997321940988794469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405899998214627325862979 608849997321940988794469)
        ·
          refine ⟨114159374497863935398963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 608849997321940988794469 114159374497863935398963)
          ·
            refine ⟨171239061746795903098445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114159374497863935398963 171239061746795903098445)
            ·
              refine ⟨64214648155048463661917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171239061746795903098445 64214648155048463661917)
              ·
                refine ⟨24080493058143173873219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64214648155048463661917 24080493058143173873219)
                ·
                  rfl

theorem cell19_79138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_79138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79138 prefixEnd_79138 := by exact prefixLift 79138
  have htrace : WordTrace (prefixWord ++ tailWord_79138) baseStart_79138 baseEnd_79138 := by
    simpa [prefixWord, tailWord_79138, baseEnd_79138] using wordTrace_append hprefix tailTrace_79138
  have hstable : (prefixWord ++ tailWord_79138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79138).length < 2 ^ (prefixWord ++ tailWord_79138).sum := by decide
  have hdescent : baseEnd_79138 < baseStart_79138 := by decide
  rcases family_descends (prefixWord ++ tailWord_79138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79140 : List Nat := [2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_79140 : Nat := 118140960795 + 79140 * 2 ^ 59
def prefixEnd_79140 : Nat := 4983230072969 + 3 ^ 40 * 79140 * 2
def baseEnd_79140 : Nat := 24081101627807761828769

theorem tailTrace_79140 : CollatzResearch.WordTrace tailWord_79140 prefixEnd_79140 24081101627807761828769 := by
  unfold tailWord_79140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443236466648385440521437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1924315288864513920695249 1443236466648385440521437)
  ·
    refine ⟨541213674993144540195539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1443236466648385440521437 541213674993144540195539)
    ·
      refine ⟨811820512489716810293309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541213674993144540195539 811820512489716810293309)
      ·
        refine ⟨304432692183643803859991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 811820512489716810293309 304432692183643803859991)
        ·
          refine ⟨456649038275465705789987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304432692183643803859991 456649038275465705789987)
          ·
            refine ⟨684973557413198558684981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456649038275465705789987 684973557413198558684981)
            ·
              refine ⟨64216271007487364876717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 684973557413198558684981 64216271007487364876717)
              ·
                refine ⟨24081101627807761828769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64216271007487364876717 24081101627807761828769)
                ·
                  rfl

theorem cell19_79140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_79140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79140 prefixEnd_79140 := by exact prefixLift 79140
  have htrace : WordTrace (prefixWord ++ tailWord_79140) baseStart_79140 baseEnd_79140 := by
    simpa [prefixWord, tailWord_79140, baseEnd_79140] using wordTrace_append hprefix tailTrace_79140
  have hstable : (prefixWord ++ tailWord_79140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79140).length < 2 ^ (prefixWord ++ tailWord_79140).sum := by decide
  have hdescent : baseEnd_79140 < baseStart_79140 := by decide
  rcases family_descends (prefixWord ++ tailWord_79140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79214 : List Nat := [4, 1, 2, 4, 1, 2, 5]
def baseStart_79214 : Nat := 118140960795 + 79214 * 2 ^ 59
def prefixEnd_79214 : Nat := 4983230072969 + 3 ^ 40 * 79214 * 2
def baseEnd_79214 : Nat := 8034539568465838728041

theorem tailTrace_79214 : CollatzResearch.WordTrace tailWord_79214 prefixEnd_79214 8034539568465838728041 := by
  unfold tailWord_79214
  simp only [CollatzResearch.WordTrace]
  refine ⟨361146491878585189904587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1926114623352454346157797 361146491878585189904587)
  ·
    refine ⟨541719737817877784856881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361146491878585189904587 541719737817877784856881)
    ·
      refine ⟨406289803363408338642661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 541719737817877784856881 406289803363408338642661)
      ·
        refine ⟨76179338130639063495499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 406289803363408338642661 76179338130639063495499)
        ·
          refine ⟨114269007195958595243249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76179338130639063495499 114269007195958595243249)
          ·
            refine ⟨85701755396968946432437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114269007195958595243249 85701755396968946432437)
            ·
              refine ⟨8034539568465838728041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85701755396968946432437 8034539568465838728041)
              ·
                rfl

theorem cell19_79214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_79214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79214 prefixEnd_79214 := by exact prefixLift 79214
  have htrace : WordTrace (prefixWord ++ tailWord_79214) baseStart_79214 baseEnd_79214 := by
    simpa [prefixWord, tailWord_79214, baseEnd_79214] using wordTrace_append hprefix tailTrace_79214
  have hstable : (prefixWord ++ tailWord_79214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79214).length < 2 ^ (prefixWord ++ tailWord_79214).sum := by decide
  have hdescent : baseEnd_79214 < baseStart_79214 := by decide
  rcases family_descends (prefixWord ++ tailWord_79214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79353 : List Nat := [1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_79353 : Nat := 118140960795 + 79353 * 2 ^ 59
def prefixEnd_79353 : Nat := 4983230072969 + 3 ^ 40 * 79353 * 2
def baseEnd_79353 : Nat := 24145914297086379094855

theorem tailTrace_79353 : CollatzResearch.WordTrace tailWord_79353 prefixEnd_79353 24145914297086379094855 := by
  unfold tailWord_79353
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894241681525108258546713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929494454350072172364475 2894241681525108258546713)
  ·
    refine ⟨2170681261143831193910035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2894241681525108258546713 2170681261143831193910035)
    ·
      refine ⟨3256021891715746790865053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170681261143831193910035 3256021891715746790865053)
      ·
        refine ⟨1221008209393405046574395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3256021891715746790865053 1221008209393405046574395)
        ·
          refine ⟨1831512314090107569861593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221008209393405046574395 1831512314090107569861593)
          ·
            refine ⟨1373634235567580677396195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831512314090107569861593 1373634235567580677396195)
            ·
              refine ⟨2060451353351371016094293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373634235567580677396195 2060451353351371016094293)
              ·
                refine ⟨24145914297086379094855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2060451353351371016094293 24145914297086379094855)
                ·
                  rfl

theorem cell19_79353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_79353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79353 prefixEnd_79353 := by exact prefixLift 79353
  have htrace : WordTrace (prefixWord ++ tailWord_79353) baseStart_79353 baseEnd_79353 := by
    simpa [prefixWord, tailWord_79353, baseEnd_79353] using wordTrace_append hprefix tailTrace_79353
  have hstable : (prefixWord ++ tailWord_79353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79353).length < 2 ^ (prefixWord ++ tailWord_79353).sum := by decide
  have hdescent : baseEnd_79353 < baseStart_79353 := by decide
  rcases family_descends (prefixWord ++ tailWord_79353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79364 : List Nat := [2, 3, 2, 3, 3, 1, 2, 3]
def baseStart_79364 : Nat := 118140960795 + 79364 * 2 ^ 59
def prefixEnd_79364 : Nat := 4983230072969 + 3 ^ 40 * 79364 * 2
def baseEnd_79364 : Nat := 24149261430241612850381

theorem tailTrace_79364 : CollatzResearch.WordTrace tailWord_79364 prefixEnd_79364 24149261430241612850381 := by
  unfold tailWord_79364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447321442242628568598573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1929761922990171424798097 1447321442242628568598573)
  ·
    refine ⟨542745540840985713224465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1447321442242628568598573 542745540840985713224465)
    ·
      refine ⟨407059155630739284918349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542745540840985713224465 407059155630739284918349)
      ·
        refine ⟨152647183361527231844381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407059155630739284918349 152647183361527231844381)
        ·
          refine ⟨57242693760572711941643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152647183361527231844381 57242693760572711941643)
          ·
            refine ⟨85864040640859067912465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57242693760572711941643 85864040640859067912465)
            ·
              refine ⟨64398030480644300934349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85864040640859067912465 64398030480644300934349)
              ·
                refine ⟨24149261430241612850381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64398030480644300934349 24149261430241612850381)
                ·
                  rfl

theorem cell19_79364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_79364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79364 prefixEnd_79364 := by exact prefixLift 79364
  have htrace : WordTrace (prefixWord ++ tailWord_79364) baseStart_79364 baseEnd_79364 := by
    simpa [prefixWord, tailWord_79364, baseEnd_79364] using wordTrace_append hprefix tailTrace_79364
  have hstable : (prefixWord ++ tailWord_79364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79364).length < 2 ^ (prefixWord ++ tailWord_79364).sum := by decide
  have hdescent : baseEnd_79364 < baseStart_79364 := by decide
  rcases family_descends (prefixWord ++ tailWord_79364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79370 : List Nat := [3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_79370 : Nat := 118140960795 + 79370 * 2 ^ 59
def prefixEnd_79370 : Nat := 4983230072969 + 3 ^ 40 * 79370 * 2
def baseEnd_79370 : Nat := 24151087139235376717031

theorem tailTrace_79370 : CollatzResearch.WordTrace tailWord_79370 prefixEnd_79370 24151087139235376717031 := by
  unfold tailWord_79370
  simp only [CollatzResearch.WordTrace]
  refine ⟨723715430615880040478891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1929907814975680107943709 723715430615880040478891)
  ·
    refine ⟨1085573145923820060718337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723715430615880040478891 1085573145923820060718337)
    ·
      refine ⟨814179859442865045538753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085573145923820060718337 814179859442865045538753)
      ·
        refine ⟨610634894582148784154065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814179859442865045538753 610634894582148784154065)
        ·
          refine ⟨457976170936611588115549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610634894582148784154065 457976170936611588115549)
          ·
            refine ⟨171741064101229345543331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 457976170936611588115549 171741064101229345543331)
            ·
              refine ⟨257611596151844018314997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171741064101229345543331 257611596151844018314997)
              ·
                refine ⟨24151087139235376717031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 257611596151844018314997 24151087139235376717031)
                ·
                  rfl

theorem cell19_79370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_79370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79370 prefixEnd_79370 := by exact prefixLift 79370
  have htrace : WordTrace (prefixWord ++ tailWord_79370) baseStart_79370 baseEnd_79370 := by
    simpa [prefixWord, tailWord_79370, baseEnd_79370] using wordTrace_append hprefix tailTrace_79370
  have hstable : (prefixWord ++ tailWord_79370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79370).length < 2 ^ (prefixWord ++ tailWord_79370).sum := by decide
  have hdescent : baseEnd_79370 < baseStart_79370 := by decide
  rcases family_descends (prefixWord ++ tailWord_79370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79391 : List Nat := [1, 1, 2, 4, 1, 1, 9]
def baseStart_79391 : Nat := 118140960795 + 79391 * 2 ^ 59
def prefixEnd_79391 : Nat := 4983230072969 + 3 ^ 40 * 79391 * 2
def baseEnd_79391 : Nat := 8052492373571183416769

theorem tailTrace_79391 : CollatzResearch.WordTrace tailWord_79391 prefixEnd_79391 8052492373571183416769 := by
  unfold tailWord_79391
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895627655387440748430027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1930418436924960498953351 2895627655387440748430027)
  ·
    refine ⟨4343441483081161122645041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2895627655387440748430027 4343441483081161122645041)
    ·
      refine ⟨3257581112310870841983781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4343441483081161122645041 3257581112310870841983781)
      ·
        refine ⟨610796458558288282871959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3257581112310870841983781 610796458558288282871959)
        ·
          refine ⟨916194687837432424307939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610796458558288282871959 916194687837432424307939)
          ·
            refine ⟨1374292031756148636461909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916194687837432424307939 1374292031756148636461909)
            ·
              refine ⟨8052492373571183416769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1374292031756148636461909 8052492373571183416769)
              ·
                rfl

theorem cell19_79391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_79391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79391 prefixEnd_79391 := by exact prefixLift 79391
  have htrace : WordTrace (prefixWord ++ tailWord_79391) baseStart_79391 baseEnd_79391 := by
    simpa [prefixWord, tailWord_79391, baseEnd_79391] using wordTrace_append hprefix tailTrace_79391
  have hstable : (prefixWord ++ tailWord_79391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79391).length < 2 ^ (prefixWord ++ tailWord_79391).sum := by decide
  have hdescent : baseEnd_79391 < baseStart_79391 := by decide
  rcases family_descends (prefixWord ++ tailWord_79391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79406 : List Nat := [4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_79406 : Nat := 118140960795 + 79406 * 2 ^ 59
def prefixEnd_79406 : Nat := 4983230072969 + 3 ^ 40 * 79406 * 2
def baseEnd_79406 : Nat := 24162041393197959916933

theorem tailTrace_79406 : CollatzResearch.WordTrace tailWord_79406 prefixEnd_79406 24162041393197959916933 := by
  unfold tailWord_79406
  simp only [CollatzResearch.WordTrace]
  refine ⟨362021843791637288778259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1930783166888732206817381 362021843791637288778259)
  ·
    refine ⟨543032765687455933167389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362021843791637288778259 543032765687455933167389)
    ·
      refine ⟨203637287132795974937771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 543032765687455933167389 203637287132795974937771)
      ·
        refine ⟨305455930699193962406657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203637287132795974937771 305455930699193962406657)
        ·
          refine ⟨229091948024395471804993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305455930699193962406657 229091948024395471804993)
          ·
            refine ⟨171818961018296603853745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229091948024395471804993 171818961018296603853745)
            ·
              refine ⟨128864220763722452890309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171818961018296603853745 128864220763722452890309)
              ·
                refine ⟨24162041393197959916933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128864220763722452890309 24162041393197959916933)
                ·
                  rfl

theorem cell19_79406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_79406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79406 prefixEnd_79406 := by exact prefixLift 79406
  have htrace : WordTrace (prefixWord ++ tailWord_79406) baseStart_79406 baseEnd_79406 := by
    simpa [prefixWord, tailWord_79406, baseEnd_79406] using wordTrace_append hprefix tailTrace_79406
  have hstable : (prefixWord ++ tailWord_79406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79406).length < 2 ^ (prefixWord ++ tailWord_79406).sum := by decide
  have hdescent : baseEnd_79406 < baseStart_79406 := by decide
  rcases family_descends (prefixWord ++ tailWord_79406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79429 : List Nat := [1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_79429 : Nat := 118140960795 + 79429 * 2 ^ 59
def prefixEnd_79429 : Nat := 4983230072969 + 3 ^ 40 * 79429 * 2
def baseEnd_79429 : Nat := 24169039944340721405759

theorem tailTrace_79429 : CollatzResearch.WordTrace tailWord_79429 prefixEnd_79429 24169039944340721405759 := by
  unfold tailWord_79429
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897013629249773238313341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1931342419499848825542227 2897013629249773238313341)
  ·
    refine ⟨1086380110968664964367503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2897013629249773238313341 1086380110968664964367503)
    ·
      refine ⟨1629570166452997446551255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086380110968664964367503 1629570166452997446551255)
      ·
        refine ⟨2444355249679496169826883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629570166452997446551255 2444355249679496169826883)
        ·
          refine ⟨3666532874519244254740325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444355249679496169826883 3666532874519244254740325)
          ·
            refine ⟨687474913972358297763811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3666532874519244254740325 687474913972358297763811)
            ·
              refine ⟨1031212370958537446645717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687474913972358297763811 1031212370958537446645717)
              ·
                refine ⟨24169039944340721405759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1031212370958537446645717 24169039944340721405759)
                ·
                  rfl

theorem cell19_79429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_79429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79429 prefixEnd_79429 := by exact prefixLift 79429
  have htrace : WordTrace (prefixWord ++ tailWord_79429) baseStart_79429 baseEnd_79429 := by
    simpa [prefixWord, tailWord_79429, baseEnd_79429] using wordTrace_append hprefix tailTrace_79429
  have hstable : (prefixWord ++ tailWord_79429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79429).length < 2 ^ (prefixWord ++ tailWord_79429).sum := by decide
  have hdescent : baseEnd_79429 < baseStart_79429 := by decide
  rcases family_descends (prefixWord ++ tailWord_79429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79554 : List Nat := [3, 5, 1, 2, 1, 2, 5]
def baseStart_79554 : Nat := 118140960795 + 79554 * 2 ^ 59
def prefixEnd_79554 : Nat := 4983230072969 + 3 ^ 40 * 79554 * 2
def baseEnd_79554 : Nat := 8069025182792489542547

theorem tailTrace_79554 : CollatzResearch.WordTrace tailWord_79554 prefixEnd_79554 8069025182792489542547 := by
  unfold tailWord_79554
  simp only [CollatzResearch.WordTrace]
  refine ⟨725393188449229896653429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1934381835864613057742477 725393188449229896653429)
  ·
    refine ⟨68005611417115302811259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 725393188449229896653429 68005611417115302811259)
    ·
      refine ⟨102008417125672954216889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68005611417115302811259 102008417125672954216889)
      ·
        refine ⟨76506312844254715662667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102008417125672954216889 76506312844254715662667)
        ·
          refine ⟨114759469266382073494001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76506312844254715662667 114759469266382073494001)
          ·
            refine ⟨86069601949786555120501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114759469266382073494001 86069601949786555120501)
            ·
              refine ⟨8069025182792489542547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86069601949786555120501 8069025182792489542547)
              ·
                rfl

theorem cell19_79554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_79554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79554 prefixEnd_79554 := by exact prefixLift 79554
  have htrace : WordTrace (prefixWord ++ tailWord_79554) baseStart_79554 baseEnd_79554 := by
    simpa [prefixWord, tailWord_79554, baseEnd_79554] using wordTrace_append hprefix tailTrace_79554
  have hstable : (prefixWord ++ tailWord_79554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79554).length < 2 ^ (prefixWord ++ tailWord_79554).sum := by decide
  have hdescent : baseEnd_79554 < baseStart_79554 := by decide
  rcases family_descends (prefixWord ++ tailWord_79554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79634 : List Nat := [3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_79634 : Nat := 118140960795 + 79634 * 2 ^ 59
def prefixEnd_79634 : Nat := 4983230072969 + 3 ^ 40 * 79634 * 2
def baseEnd_79634 : Nat := 24231418334960986849645

theorem tailTrace_79634 : CollatzResearch.WordTrace tailWord_79634 prefixEnd_79634 24231418334960986849645 := by
  unfold tailWord_79634
  simp only [CollatzResearch.WordTrace]
  refine ⟨726122648376773312381489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1936327062338062166350637 726122648376773312381489)
  ·
    refine ⟨544591986282579984286117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 726122648376773312381489 544591986282579984286117)
    ·
      refine ⟨102110997427983747053647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 544591986282579984286117 102110997427983747053647)
      ·
        refine ⟨153166496141975620580471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102110997427983747053647 153166496141975620580471)
        ·
          refine ⟨229749744212963430870707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153166496141975620580471 229749744212963430870707)
          ·
            refine ⟨344624616319445146306061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229749744212963430870707 344624616319445146306061)
            ·
              refine ⟨129234231119791929864773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344624616319445146306061 129234231119791929864773)
              ·
                refine ⟨24231418334960986849645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129234231119791929864773 24231418334960986849645)
                ·
                  rfl

theorem cell19_79634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_79634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79634 prefixEnd_79634 := by exact prefixLift 79634
  have htrace : WordTrace (prefixWord ++ tailWord_79634) baseStart_79634 baseEnd_79634 := by
    simpa [prefixWord, tailWord_79634, baseEnd_79634] using wordTrace_append hprefix tailTrace_79634
  have hstable : (prefixWord ++ tailWord_79634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79634).length < 2 ^ (prefixWord ++ tailWord_79634).sum := by decide
  have hdescent : baseEnd_79634 < baseStart_79634 := by decide
  rcases family_descends (prefixWord ++ tailWord_79634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79708 : List Nat := [2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_79708 : Nat := 118140960795 + 79708 * 2 ^ 59
def prefixEnd_79708 : Nat := 4983230072969 + 3 ^ 40 * 79708 * 2
def baseEnd_79708 : Nat := 24253935412550741204999

theorem tailTrace_79708 : CollatzResearch.WordTrace tailWord_79708 prefixEnd_79708 24253935412550741204999 := by
  unfold tailWord_79708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453594797619501943859889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1938126396826002591813185 1453594797619501943859889)
  ·
    refine ⟨1090196098214626457894917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1453594797619501943859889 1090196098214626457894917)
    ·
      refine ⟨204411768415242460855297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1090196098214626457894917 204411768415242460855297)
      ·
        refine ⟨153308826311431845641473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204411768415242460855297 153308826311431845641473)
        ·
          refine ⟨114981619733573884231105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153308826311431845641473 114981619733573884231105)
          ·
            refine ⟨86236214800180413173329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114981619733573884231105 86236214800180413173329)
            ·
              refine ⟨64677161100135309879997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86236214800180413173329 64677161100135309879997)
              ·
                refine ⟨24253935412550741204999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64677161100135309879997 24253935412550741204999)
                ·
                  rfl

theorem cell19_79708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_79708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79708 prefixEnd_79708 := by exact prefixLift 79708
  have htrace : WordTrace (prefixWord ++ tailWord_79708) baseStart_79708 baseEnd_79708 := by
    simpa [prefixWord, tailWord_79708, baseEnd_79708] using wordTrace_append hprefix tailTrace_79708
  have hstable : (prefixWord ++ tailWord_79708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79708).length < 2 ^ (prefixWord ++ tailWord_79708).sum := by decide
  have hdescent : baseEnd_79708 < baseStart_79708 := by decide
  rcases family_descends (prefixWord ++ tailWord_79708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79712 : List Nat := [2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_79712 : Nat := 118140960795 + 79712 * 2 ^ 59
def prefixEnd_79712 : Nat := 4983230072969 + 3 ^ 40 * 79712 * 2
def baseEnd_79712 : Nat := 24255152551879917116099

theorem tailTrace_79712 : CollatzResearch.WordTrace tailWord_79712 prefixEnd_79712 24255152551879917116099 := by
  unfold tailWord_79712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453667743612256285432695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1938223658149675047243593 1453667743612256285432695)
  ·
    refine ⟨2180501615418384428149043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1453667743612256285432695 2180501615418384428149043)
    ·
      refine ⟨3270752423127576642223565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180501615418384428149043 3270752423127576642223565)
      ·
        refine ⟨1226532158672841240833837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3270752423127576642223565 1226532158672841240833837)
        ·
          refine ⟨459949559502315465312689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1226532158672841240833837 459949559502315465312689)
          ·
            refine ⟨344962169626736598984517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459949559502315465312689 344962169626736598984517)
            ·
              refine ⟨64680406805013112309597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344962169626736598984517 64680406805013112309597)
              ·
                refine ⟨24255152551879917116099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64680406805013112309597 24255152551879917116099)
                ·
                  rfl

theorem cell19_79712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_79712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79712 prefixEnd_79712 := by exact prefixLift 79712
  have htrace : WordTrace (prefixWord ++ tailWord_79712) baseStart_79712 baseEnd_79712 := by
    simpa [prefixWord, tailWord_79712, baseEnd_79712] using wordTrace_append hprefix tailTrace_79712
  have hstable : (prefixWord ++ tailWord_79712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79712).length < 2 ^ (prefixWord ++ tailWord_79712).sum := by decide
  have hdescent : baseEnd_79712 < baseStart_79712 := by decide
  rcases family_descends (prefixWord ++ tailWord_79712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79980 : List Nat := [2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_79980 : Nat := 118140960795 + 79980 * 2 ^ 59
def prefixEnd_79980 : Nat := 4983230072969 + 3 ^ 40 * 79980 * 2
def baseEnd_79980 : Nat := 24336700886934703159813

theorem tailTrace_79980 : CollatzResearch.WordTrace tailWord_79980 prefixEnd_79980 24336700886934703159813 := by
  unfold tailWord_79980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458555125126797170810697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1944740166835729561080929 1458555125126797170810697)
  ·
    refine ⟨1093916343845097878108023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1458555125126797170810697 1093916343845097878108023)
    ·
      refine ⟨1640874515767646817162035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093916343845097878108023 1640874515767646817162035)
      ·
        refine ⟨2461311773651470225743053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640874515767646817162035 2461311773651470225743053)
        ·
          refine ⟨922991915119301334653645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2461311773651470225743053 922991915119301334653645)
          ·
            refine ⟨346121968169738000495117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 922991915119301334653645 346121968169738000495117)
            ·
              refine ⟨129795738063651750185669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346121968169738000495117 129795738063651750185669)
              ·
                refine ⟨24336700886934703159813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129795738063651750185669 24336700886934703159813)
                ·
                  rfl

theorem cell19_79980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_79980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79980 prefixEnd_79980 := by exact prefixLift 79980
  have htrace : WordTrace (prefixWord ++ tailWord_79980) baseStart_79980 baseEnd_79980 := by
    simpa [prefixWord, tailWord_79980, baseEnd_79980] using wordTrace_append hprefix tailTrace_79980
  have hstable : (prefixWord ++ tailWord_79980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79980).length < 2 ^ (prefixWord ++ tailWord_79980).sum := by decide
  have hdescent : baseEnd_79980 < baseStart_79980 := by decide
  rcases family_descends (prefixWord ++ tailWord_79980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79997 : List Nat := [1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_79997 : Nat := 118140960795 + 79997 * 2 ^ 59
def prefixEnd_79997 : Nat := 4983230072969 + 3 ^ 40 * 79997 * 2
def baseEnd_79997 : Nat := 24341873729083700781989

theorem tailTrace_79997 : CollatzResearch.WordTrace tailWord_79997 prefixEnd_79997 24341873729083700781989 := by
  unfold tailWord_79997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917730291192006244990245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1945153527461337496660163 2917730291192006244990245)
  ·
    refine ⟨547074429598501170935671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2917730291192006244990245 547074429598501170935671)
    ·
      refine ⟨820611644397751756403507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547074429598501170935671 820611644397751756403507)
      ·
        refine ⟨1230917466596627634605261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820611644397751756403507 1230917466596627634605261)
        ·
          refine ⟨461594049973735362976973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1230917466596627634605261 461594049973735362976973)
          ·
            refine ⟨173097768740150761116365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461594049973735362976973 173097768740150761116365)
            ·
              refine ⟨64911663277556535418637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173097768740150761116365 64911663277556535418637)
              ·
                refine ⟨24341873729083700781989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64911663277556535418637 24341873729083700781989)
                ·
                  rfl

theorem cell19_79997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_79997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_79997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_79997 prefixEnd_79997 := by exact prefixLift 79997
  have htrace : WordTrace (prefixWord ++ tailWord_79997) baseStart_79997 baseEnd_79997 := by
    simpa [prefixWord, tailWord_79997, baseEnd_79997] using wordTrace_append hprefix tailTrace_79997
  have hstable : (prefixWord ++ tailWord_79997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79997).length < 2 ^ (prefixWord ++ tailWord_79997).sum := by decide
  have hdescent : baseEnd_79997 < baseStart_79997 := by decide
  rcases family_descends (prefixWord ++ tailWord_79997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80018 : List Nat := [3, 2, 3, 1, 1, 1, 8]
def baseStart_80018 : Nat := 118140960795 + 80018 * 2 ^ 59
def prefixEnd_80018 : Nat := 4983230072969 + 3 ^ 40 * 80018 * 2
def baseEnd_80018 : Nat := 8116087903520624771755

theorem tailTrace_80018 : CollatzResearch.WordTrace tailWord_80018 prefixEnd_80018 8116087903520624771755 := by
  unfold tailWord_80018
  simp only [CollatzResearch.WordTrace]
  refine ⟨729624056028981707876177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1945664149410617887669805 729624056028981707876177)
  ·
    refine ⟨547218042021736280907133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 729624056028981707876177 547218042021736280907133)
    ·
      refine ⟨205206765758151105340175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 547218042021736280907133 205206765758151105340175)
      ·
        refine ⟨307810148637226658010263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205206765758151105340175 307810148637226658010263)
        ·
          refine ⟨461715222955839987015395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307810148637226658010263 461715222955839987015395)
          ·
            refine ⟨692572834433759980523093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461715222955839987015395 692572834433759980523093)
            ·
              refine ⟨8116087903520624771755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 692572834433759980523093 8116087903520624771755)
              ·
                rfl

theorem cell19_80018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_80018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80018 prefixEnd_80018 := by exact prefixLift 80018
  have htrace : WordTrace (prefixWord ++ tailWord_80018) baseStart_80018 baseEnd_80018 := by
    simpa [prefixWord, tailWord_80018, baseEnd_80018] using wordTrace_append hprefix tailTrace_80018
  have hstable : (prefixWord ++ tailWord_80018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80018).length < 2 ^ (prefixWord ++ tailWord_80018).sum := by decide
  have hdescent : baseEnd_80018 < baseStart_80018 := by decide
  rcases family_descends (prefixWord ++ tailWord_80018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80115 : List Nat := [1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_80115 : Nat := 118140960795 + 80115 * 2 ^ 59
def prefixEnd_80115 : Nat := 4983230072969 + 3 ^ 40 * 80115 * 2
def baseEnd_80115 : Nat := 24377779339294390159445

theorem tailTrace_80115 : CollatzResearch.WordTrace tailWord_80115 prefixEnd_80115 24377779339294390159445 := by
  unfold tailWord_80115
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922034104764512397785799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948022736509674931857199 2922034104764512397785799)
  ·
    refine ⟨4383051157146768596678699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2922034104764512397785799 4383051157146768596678699)
    ·
      refine ⟨6574576735720152895018049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383051157146768596678699 6574576735720152895018049)
      ·
        refine ⟨4930932551790114671263537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6574576735720152895018049 4930932551790114671263537)
        ·
          refine ⟨3698199413842586003447653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4930932551790114671263537 3698199413842586003447653)
          ·
            refine ⟨693412390095484875646435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3698199413842586003447653 693412390095484875646435)
            ·
              refine ⟨1040118585143227313469653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693412390095484875646435 1040118585143227313469653)
              ·
                refine ⟨24377779339294390159445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1040118585143227313469653 24377779339294390159445)
                ·
                  rfl

theorem cell19_80115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_80115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80115 prefixEnd_80115 := by exact prefixLift 80115
  have htrace : WordTrace (prefixWord ++ tailWord_80115) baseStart_80115 baseEnd_80115 := by
    simpa [prefixWord, tailWord_80115, baseEnd_80115] using wordTrace_append hprefix tailTrace_80115
  have hstable : (prefixWord ++ tailWord_80115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80115).length < 2 ^ (prefixWord ++ tailWord_80115).sum := by decide
  have hdescent : baseEnd_80115 < baseStart_80115 := by decide
  rcases family_descends (prefixWord ++ tailWord_80115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80132 : List Nat := [2, 3, 2, 2, 3, 7]
def baseStart_80132 : Nat := 118140960795 + 80132 * 2 ^ 59
def prefixEnd_80132 : Nat := 4983230072969 + 3 ^ 40 * 80132 * 2
def baseEnd_80132 : Nat := 2709216909049265309069

theorem tailTrace_80132 : CollatzResearch.WordTrace tailWord_80132 prefixEnd_80132 2709216909049265309069 := by
  unfold tailWord_80132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461327072851462150577325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1948436097135282867436433 1461327072851462150577325)
  ·
    refine ⟨547997652319298306466497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1461327072851462150577325 547997652319298306466497)
    ·
      refine ⟨410998239239473729849873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 547997652319298306466497 410998239239473729849873)
      ·
        refine ⟨308248679429605297387405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410998239239473729849873 308248679429605297387405)
        ·
          refine ⟨115593254786101986520277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308248679429605297387405 115593254786101986520277)
          ·
            refine ⟨2709216909049265309069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 115593254786101986520277 2709216909049265309069)
            ·
              rfl

theorem cell19_80132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_80132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80132 prefixEnd_80132 := by exact prefixLift 80132
  have htrace : WordTrace (prefixWord ++ tailWord_80132) baseStart_80132 baseEnd_80132 := by
    simpa [prefixWord, tailWord_80132, baseEnd_80132] using wordTrace_append hprefix tailTrace_80132
  have hstable : (prefixWord ++ tailWord_80132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80132).length < 2 ^ (prefixWord ++ tailWord_80132).sum := by decide
  have hdescent : baseEnd_80132 < baseStart_80132 := by decide
  rcases family_descends (prefixWord ++ tailWord_80132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80151 : List Nat := [1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_80151 : Nat := 118140960795 + 80151 * 2 ^ 59
def prefixEnd_80151 : Nat := 4983230072969 + 3 ^ 40 * 80151 * 2
def baseEnd_80151 : Nat := 24388733593256973359347

theorem tailTrace_80151 : CollatzResearch.WordTrace tailWord_80151 prefixEnd_80151 24388733593256973359347 := by
  unfold tailWord_80151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923347132634090546096307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948898088422727030730871 2923347132634090546096307)
  ·
    refine ⟨4385020698951135819144461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923347132634090546096307 4385020698951135819144461)
    ·
      refine ⟨1644382762106675932179173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4385020698951135819144461 1644382762106675932179173)
      ·
        refine ⟨308321767895001737283595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1644382762106675932179173 308321767895001737283595)
        ·
          refine ⟨462482651842502605925393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308321767895001737283595 462482651842502605925393)
          ·
            refine ⟨346861988881876954444045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462482651842502605925393 346861988881876954444045)
            ·
              refine ⟨130073245830703857916517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346861988881876954444045 130073245830703857916517)
              ·
                refine ⟨24388733593256973359347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130073245830703857916517 24388733593256973359347)
                ·
                  rfl

theorem cell19_80151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_80151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80151 prefixEnd_80151 := by exact prefixLift 80151
  have htrace : WordTrace (prefixWord ++ tailWord_80151) baseStart_80151 baseEnd_80151 := by
    simpa [prefixWord, tailWord_80151, baseEnd_80151] using wordTrace_append hprefix tailTrace_80151
  have hstable : (prefixWord ++ tailWord_80151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80151).length < 2 ^ (prefixWord ++ tailWord_80151).sum := by decide
  have hdescent : baseEnd_80151 < baseStart_80151 := by decide
  rcases family_descends (prefixWord ++ tailWord_80151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80172 : List Nat := [2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_80172 : Nat := 118140960795 + 80172 * 2 ^ 59
def prefixEnd_80172 : Nat := 4983230072969 + 3 ^ 40 * 80172 * 2
def baseEnd_80172 : Nat := 24395123574735146892623

theorem tailTrace_80172 : CollatzResearch.WordTrace tailWord_80172 prefixEnd_80172 24395123574735146892623 := by
  unfold tailWord_80172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462056532779005566305385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1949408710372007421740513 1462056532779005566305385)
  ·
    refine ⟨1096542399584254174729039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1462056532779005566305385 1096542399584254174729039)
    ·
      refine ⟨1644813599376381262093559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1096542399584254174729039 1644813599376381262093559)
      ·
        refine ⟨2467220399064571893140339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644813599376381262093559 2467220399064571893140339)
        ·
          refine ⟨3700830598596857839710509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467220399064571893140339 3700830598596857839710509)
          ·
            refine ⟨1387811474473821689891441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3700830598596857839710509 1387811474473821689891441)
            ·
              refine ⟨1040858605855366267418581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387811474473821689891441 1040858605855366267418581)
              ·
                refine ⟨24395123574735146892623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1040858605855366267418581 24395123574735146892623)
                ·
                  rfl

theorem cell19_80172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_80172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80172 prefixEnd_80172 := by exact prefixLift 80172
  have htrace : WordTrace (prefixWord ++ tailWord_80172) baseStart_80172 baseEnd_80172 := by
    simpa [prefixWord, tailWord_80172, baseEnd_80172] using wordTrace_append hprefix tailTrace_80172
  have hstable : (prefixWord ++ tailWord_80172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80172).length < 2 ^ (prefixWord ++ tailWord_80172).sum := by decide
  have hdescent : baseEnd_80172 < baseStart_80172 := by decide
  rcases family_descends (prefixWord ++ tailWord_80172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80191 : List Nat := [1, 1, 2, 2, 4, 1, 8]
def baseStart_80191 : Nat := 118140960795 + 80191 * 2 ^ 59
def prefixEnd_80191 : Nat := 4983230072969 + 3 ^ 40 * 80191 * 2
def baseEnd_80191 : Nat := 8133634995516244156783

theorem tailTrace_80191 : CollatzResearch.WordTrace tailWord_80191 prefixEnd_80191 8133634995516244156783 := by
  unfold tailWord_80191
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924806052489177377552427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1949870701659451585034951 2924806052489177377552427)
  ·
    refine ⟨4387209078733766066328641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2924806052489177377552427 4387209078733766066328641)
    ·
      refine ⟨3290406809050324549746481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4387209078733766066328641 3290406809050324549746481)
      ·
        refine ⟨2467805106787743412309861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3290406809050324549746481 2467805106787743412309861)
        ·
          refine ⟨462713457522701889808099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2467805106787743412309861 462713457522701889808099)
          ·
            refine ⟨694070186284052834712149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462713457522701889808099 694070186284052834712149)
            ·
              refine ⟨8133634995516244156783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 694070186284052834712149 8133634995516244156783)
              ·
                rfl

theorem cell19_80191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_80191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80191 prefixEnd_80191 := by exact prefixLift 80191
  have htrace : WordTrace (prefixWord ++ tailWord_80191) baseStart_80191 baseEnd_80191 := by
    simpa [prefixWord, tailWord_80191, baseEnd_80191] using wordTrace_append hprefix tailTrace_80191
  have hstable : (prefixWord ++ tailWord_80191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80191).length < 2 ^ (prefixWord ++ tailWord_80191).sum := by decide
  have hdescent : baseEnd_80191 < baseStart_80191 := by decide
  rcases family_descends (prefixWord ++ tailWord_80191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80265 : List Nat := [1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_80265 : Nat := 118140960795 + 80265 * 2 ^ 59
def prefixEnd_80265 : Nat := 4983230072969 + 3 ^ 40 * 80265 * 2
def baseEnd_80265 : Nat := 24423422064138486825703

theorem tailTrace_80265 : CollatzResearch.WordTrace tailWord_80265 prefixEnd_80265 24423422064138486825703 := by
  unfold tailWord_80265
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927505054221088015746249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1951670036147392010497499 2927505054221088015746249)
  ·
    refine ⟨2195628790665816011809687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2927505054221088015746249 2195628790665816011809687)
    ·
      refine ⟨3293443185998724017714531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2195628790665816011809687 3293443185998724017714531)
      ·
        refine ⟨4940164778998086026571797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293443185998724017714531 4940164778998086026571797)
        ·
          refine ⟨231570224015535282495553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4940164778998086026571797 231570224015535282495553)
          ·
            refine ⟨173677668011651461871665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231570224015535282495553 173677668011651461871665)
            ·
              refine ⟨130258251008738596403749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173677668011651461871665 130258251008738596403749)
              ·
                refine ⟨24423422064138486825703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130258251008738596403749 24423422064138486825703)
                ·
                  rfl

theorem cell19_80265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_80265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80265 prefixEnd_80265 := by exact prefixLift 80265
  have htrace : WordTrace (prefixWord ++ tailWord_80265) baseStart_80265 baseEnd_80265 := by
    simpa [prefixWord, tailWord_80265, baseEnd_80265] using wordTrace_append hprefix tailTrace_80265
  have hstable : (prefixWord ++ tailWord_80265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80265).length < 2 ^ (prefixWord ++ tailWord_80265).sum := by decide
  have hdescent : baseEnd_80265 < baseStart_80265 := by decide
  rcases family_descends (prefixWord ++ tailWord_80265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80267 : List Nat := [1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_80267 : Nat := 118140960795 + 80267 * 2 ^ 59
def prefixEnd_80267 : Nat := 4983230072969 + 3 ^ 40 * 80267 * 2
def baseEnd_80267 : Nat := 24424030633803074781253

theorem tailTrace_80267 : CollatzResearch.WordTrace tailWord_80267 prefixEnd_80267 24424030633803074781253 := by
  unfold tailWord_80267
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927578000213842357319055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1951718666809228238212703 2927578000213842357319055)
  ·
    refine ⟨4391367000320763535978583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2927578000213842357319055 4391367000320763535978583)
    ·
      refine ⟨6587050500481145303967875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391367000320763535978583 6587050500481145303967875)
      ·
        refine ⟨9880575750721717955951813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6587050500481145303967875 9880575750721717955951813)
        ·
          refine ⟨1852607953260322116740965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9880575750721717955951813 1852607953260322116740965)
          ·
            refine ⟨347363991236310396888931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1852607953260322116740965 347363991236310396888931)
            ·
              refine ⟨521045986854465595333397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347363991236310396888931 521045986854465595333397)
              ·
                refine ⟨24424030633803074781253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 521045986854465595333397 24424030633803074781253)
                ·
                  rfl

theorem cell19_80267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_80267 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80267 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80267 prefixEnd_80267 := by exact prefixLift 80267
  have htrace : WordTrace (prefixWord ++ tailWord_80267) baseStart_80267 baseEnd_80267 := by
    simpa [prefixWord, tailWord_80267, baseEnd_80267] using wordTrace_append hprefix tailTrace_80267
  have hstable : (prefixWord ++ tailWord_80267).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80267).length < 2 ^ (prefixWord ++ tailWord_80267).sum := by decide
  have hdescent : baseEnd_80267 < baseStart_80267 := by decide
  rcases family_descends (prefixWord ++ tailWord_80267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80301 : List Nat := [1, 5, 2, 2, 3, 6]
def baseStart_80301 : Nat := 118140960795 + 80301 * 2 ^ 59
def prefixEnd_80301 : Nat := 4983230072969 + 3 ^ 40 * 80301 * 2
def baseEnd_80301 : Nat := 2714930702011230002845

theorem tailTrace_80301 : CollatzResearch.WordTrace tailWord_80301 prefixEnd_80301 2714930702011230002845 := by
  unfold tailWord_80301
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928818082090666164056757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1952545388060444109371171 2928818082090666164056757)
  ·
    refine ⟨274576695195999952880321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2928818082090666164056757 274576695195999952880321)
    ·
      refine ⟨205932521396999964660241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274576695195999952880321 205932521396999964660241)
      ·
        refine ⟨154449391047749973495181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205932521396999964660241 154449391047749973495181)
        ·
          refine ⟨57918521642906240060693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154449391047749973495181 57918521642906240060693)
          ·
            refine ⟨2714930702011230002845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57918521642906240060693 2714930702011230002845)
            ·
              rfl

theorem cell19_80301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_80301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80301 prefixEnd_80301 := by exact prefixLift 80301
  have htrace : WordTrace (prefixWord ++ tailWord_80301) baseStart_80301 baseEnd_80301 := by
    simpa [prefixWord, tailWord_80301, baseEnd_80301] using wordTrace_append hprefix tailTrace_80301
  have hstable : (prefixWord ++ tailWord_80301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80301).length < 2 ^ (prefixWord ++ tailWord_80301).sum := by decide
  have hdescent : baseEnd_80301 < baseStart_80301 := by decide
  rcases family_descends (prefixWord ++ tailWord_80301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80305 : List Nat := [1, 2, 2, 4, 1, 9]
def baseStart_80305 : Nat := 118140960795 + 80305 * 2 ^ 59
def prefixEnd_80305 : Nat := 4983230072969 + 3 ^ 40 * 80305 * 2
def baseEnd_80305 : Nat := 2715065939714471770745

theorem tailTrace_80305 : CollatzResearch.WordTrace tailWord_80305 prefixEnd_80305 2715065939714471770745 := by
  unfold tailWord_80305
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928963974076174847202369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1952642649384116564801579 2928963974076174847202369)
  ·
    refine ⟨2196722980557131135401777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2928963974076174847202369 2196722980557131135401777)
    ·
      refine ⟨1647542235417848351551333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2196722980557131135401777 1647542235417848351551333)
      ·
        refine ⟨308914169140846565915875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1647542235417848351551333 308914169140846565915875)
        ·
          refine ⟨463371253711269848873813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308914169140846565915875 463371253711269848873813)
          ·
            refine ⟨2715065939714471770745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 463371253711269848873813 2715065939714471770745)
            ·
              rfl

theorem cell19_80305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_80305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80305 prefixEnd_80305 := by exact prefixLift 80305
  have htrace : WordTrace (prefixWord ++ tailWord_80305) baseStart_80305 baseEnd_80305 := by
    simpa [prefixWord, tailWord_80305, baseEnd_80305] using wordTrace_append hprefix tailTrace_80305
  have hstable : (prefixWord ++ tailWord_80305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80305).length < 2 ^ (prefixWord ++ tailWord_80305).sum := by decide
  have hdescent : baseEnd_80305 < baseStart_80305 := by decide
  rcases family_descends (prefixWord ++ tailWord_80305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80381 : List Nat := [1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_80381 : Nat := 118140960795 + 80381 * 2 ^ 59
def prefixEnd_80381 : Nat := 4983230072969 + 3 ^ 40 * 80381 * 2
def baseEnd_80381 : Nat := 24458719104684588247609

theorem tailTrace_80381 : CollatzResearch.WordTrace tailWord_80381 prefixEnd_80381 24458719104684588247609 := by
  unfold tailWord_80381
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931735921800839826968997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1954490614533893217979331 2931735921800839826968997)
  ·
    refine ⟨549700485337657467556687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2931735921800839826968997 549700485337657467556687)
    ·
      refine ⟨824550728006486201335031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549700485337657467556687 824550728006486201335031)
      ·
        refine ⟨1236826092009729302002547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824550728006486201335031 1236826092009729302002547)
        ·
          refine ⟨1855239138014593953003821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236826092009729302002547 1855239138014593953003821)
          ·
            refine ⟨695714676755472732376433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1855239138014593953003821 695714676755472732376433)
            ·
              refine ⟨521786007566604549282325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695714676755472732376433 521786007566604549282325)
              ·
                refine ⟨24458719104684588247609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 521786007566604549282325 24458719104684588247609)
                ·
                  rfl

theorem cell19_80381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_80381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80381 prefixEnd_80381 := by exact prefixLift 80381
  have htrace : WordTrace (prefixWord ++ tailWord_80381) baseStart_80381 baseEnd_80381 := by
    simpa [prefixWord, tailWord_80381, baseEnd_80381] using wordTrace_append hprefix tailTrace_80381
  have hstable : (prefixWord ++ tailWord_80381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80381).length < 2 ^ (prefixWord ++ tailWord_80381).sum := by decide
  have hdescent : baseEnd_80381 < baseStart_80381 := by decide
  rcases family_descends (prefixWord ++ tailWord_80381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80390 : List Nat := [6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_80390 : Nat := 118140960795 + 80390 * 2 ^ 59
def prefixEnd_80390 : Nat := 4983230072969 + 3 ^ 40 * 80390 * 2
def baseEnd_80390 : Nat := 24461457668175234047585

theorem tailTrace_80390 : CollatzResearch.WordTrace tailWord_80390 prefixEnd_80390 24461457668175234047585 := by
  unfold tailWord_80390
  simp only [CollatzResearch.WordTrace]
  refine ⟨91627005586507323876457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1954709452512156242697749 91627005586507323876457)
  ·
    refine ⟨68720254189880492907343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91627005586507323876457 68720254189880492907343)
    ·
      refine ⟨103080381284820739361015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68720254189880492907343 103080381284820739361015)
      ·
        refine ⟨154620571927231109041523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103080381284820739361015 154620571927231109041523)
        ·
          refine ⟨231930857890846663562285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154620571927231109041523 231930857890846663562285)
          ·
            refine ⟨86974071709067498835857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231930857890846663562285 86974071709067498835857)
            ·
              refine ⟨65230553781800624126893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86974071709067498835857 65230553781800624126893)
              ·
                refine ⟨24461457668175234047585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65230553781800624126893 24461457668175234047585)
                ·
                  rfl

theorem cell19_80390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_80390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80390 prefixEnd_80390 := by exact prefixLift 80390
  have htrace : WordTrace (prefixWord ++ tailWord_80390) baseStart_80390 baseEnd_80390 := by
    simpa [prefixWord, tailWord_80390, baseEnd_80390] using wordTrace_append hprefix tailTrace_80390
  have hstable : (prefixWord ++ tailWord_80390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80390).length < 2 ^ (prefixWord ++ tailWord_80390).sum := by decide
  have hdescent : baseEnd_80390 < baseStart_80390 := by decide
  rcases family_descends (prefixWord ++ tailWord_80390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80396 : List Nat := [2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_80396 : Nat := 118140960795 + 80396 * 2 ^ 59
def prefixEnd_80396 : Nat := 4983230072969 + 3 ^ 40 * 80396 * 2
def baseEnd_80396 : Nat := 24463283377168997914235

theorem tailTrace_80396 : CollatzResearch.WordTrace tailWord_80396 prefixEnd_80396 24463283377168997914235 := by
  unfold tailWord_80396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466141508373248694382521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1954855344497664925843361 1466141508373248694382521)
  ·
    refine ⟨1099606131279936520786891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1466141508373248694382521 1099606131279936520786891)
    ·
      refine ⟨1649409196919904781180337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099606131279936520786891 1649409196919904781180337)
      ·
        refine ⟨1237056897689928585885253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649409196919904781180337 1237056897689928585885253)
        ·
          refine ⟨231948168316861609853485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1237056897689928585885253 231948168316861609853485)
          ·
            refine ⟨86980563118823103695057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231948168316861609853485 86980563118823103695057)
            ·
              refine ⟨65235422339117327771293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86980563118823103695057 65235422339117327771293)
              ·
                refine ⟨24463283377168997914235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65235422339117327771293 24463283377168997914235)
                ·
                  rfl

theorem cell19_80396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_80396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80396 prefixEnd_80396 := by exact prefixLift 80396
  have htrace : WordTrace (prefixWord ++ tailWord_80396) baseStart_80396 baseEnd_80396 := by
    simpa [prefixWord, tailWord_80396, baseEnd_80396] using wordTrace_append hprefix tailTrace_80396
  have hstable : (prefixWord ++ tailWord_80396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80396).length < 2 ^ (prefixWord ++ tailWord_80396).sum := by decide
  have hdescent : baseEnd_80396 < baseStart_80396 := by decide
  rcases family_descends (prefixWord ++ tailWord_80396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80398 : List Nat := [4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_80398 : Nat := 118140960795 + 80398 * 2 ^ 59
def prefixEnd_80398 : Nat := 4983230072969 + 3 ^ 40 * 80398 * 2
def baseEnd_80398 : Nat := 24463891946833585869785

theorem tailTrace_80398 : CollatzResearch.WordTrace tailWord_80398 prefixEnd_80398 24463891946833585869785 := by
  unfold tailWord_80398
  simp only [CollatzResearch.WordTrace]
  refine ⟨366544495342406466292231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1954903975159501153558565 366544495342406466292231)
  ·
    refine ⟨549816743013609699438347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 366544495342406466292231 549816743013609699438347)
    ·
      refine ⟨824725114520414549157521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549816743013609699438347 824725114520414549157521)
      ·
        refine ⟨618543835890310911868141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824725114520414549157521 618543835890310911868141)
        ·
          refine ⟨231953938458866591950553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 618543835890310911868141 231953938458866591950553)
          ·
            refine ⟨173965453844149943962915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231953938458866591950553 173965453844149943962915)
            ·
              refine ⟨260948180766224915944373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173965453844149943962915 260948180766224915944373)
              ·
                refine ⟨24463891946833585869785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260948180766224915944373 24463891946833585869785)
                ·
                  rfl

theorem cell19_80398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_80398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80398 prefixEnd_80398 := by exact prefixLift 80398
  have htrace : WordTrace (prefixWord ++ tailWord_80398) baseStart_80398 baseEnd_80398 := by
    simpa [prefixWord, tailWord_80398, baseEnd_80398] using wordTrace_append hprefix tailTrace_80398
  have hstable : (prefixWord ++ tailWord_80398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80398).length < 2 ^ (prefixWord ++ tailWord_80398).sum := by decide
  have hdescent : baseEnd_80398 < baseStart_80398 := by decide
  rcases family_descends (prefixWord ++ tailWord_80398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80419 : List Nat := [1, 1, 1, 4, 4, 1, 7]
def baseStart_80419 : Nat := 118140960795 + 80419 * 2 ^ 59
def prefixEnd_80419 : Nat := 4983230072969 + 3 ^ 40 * 80419 * 2
def baseEnd_80419 : Nat := 8156760642770586467687

theorem tailTrace_80419 : CollatzResearch.WordTrace tailWord_80419 prefixEnd_80419 8156760642770586467687 := by
  unfold tailWord_80419
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933121895663172316852311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1955414597108781544568207 2933121895663172316852311)
  ·
    refine ⟨4399682843494758475278467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2933121895663172316852311 4399682843494758475278467)
    ·
      refine ⟨6599524265242137712917701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399682843494758475278467 6599524265242137712917701)
      ·
        refine ⟨1237410799732900821172069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6599524265242137712917701 1237410799732900821172069)
        ·
          refine ⟨232014524949918903969763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1237410799732900821172069 232014524949918903969763)
          ·
            refine ⟨348021787424878355954645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232014524949918903969763 348021787424878355954645)
            ·
              refine ⟨8156760642770586467687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 348021787424878355954645 8156760642770586467687)
              ·
                rfl

theorem cell19_80419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_80419 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80419 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80419 prefixEnd_80419 := by exact prefixLift 80419
  have htrace : WordTrace (prefixWord ++ tailWord_80419) baseStart_80419 baseEnd_80419 := by
    simpa [prefixWord, tailWord_80419, baseEnd_80419] using wordTrace_append hprefix tailTrace_80419
  have hstable : (prefixWord ++ tailWord_80419).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80419).length < 2 ^ (prefixWord ++ tailWord_80419).sum := by decide
  have hdescent : baseEnd_80419 < baseStart_80419 := by decide
  rcases family_descends (prefixWord ++ tailWord_80419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80476 : List Nat := [2, 2, 4, 1, 10]
def baseStart_80476 : Nat := 118140960795 + 80476 * 2 ^ 59
def prefixEnd_80476 : Nat := 4983230072969 + 3 ^ 40 * 80476 * 2
def baseEnd_80476 : Nat := 906949117176019116157

theorem tailTrace_80476 : CollatzResearch.WordTrace tailWord_80476 prefixEnd_80476 906949117176019116157 := by
  unfold tailWord_80476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467600428228335525838641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1956800570971114034451521 1467600428228335525838641)
  ·
    refine ⟨1100700321171251644378981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1467600428228335525838641 1100700321171251644378981)
    ·
      refine ⟨206381310219609683321059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1100700321171251644378981 206381310219609683321059)
      ·
        refine ⟨309571965329414524981589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206381310219609683321059 309571965329414524981589)
        ·
          refine ⟨906949117176019116157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 309571965329414524981589 906949117176019116157)
          ·
            rfl

theorem cell19_80476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 10].length) (baseStart_80476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80476 prefixEnd_80476 := by exact prefixLift 80476
  have htrace : WordTrace (prefixWord ++ tailWord_80476) baseStart_80476 baseEnd_80476 := by
    simpa [prefixWord, tailWord_80476, baseEnd_80476] using wordTrace_append hprefix tailTrace_80476
  have hstable : (prefixWord ++ tailWord_80476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80476).length < 2 ^ (prefixWord ++ tailWord_80476).sum := by decide
  have hdescent : baseEnd_80476 < baseStart_80476 := by decide
  rcases family_descends (prefixWord ++ tailWord_80476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80493 : List Nat := [1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_80493 : Nat := 118140960795 + 80493 * 2 ^ 59
def prefixEnd_80493 : Nat := 4983230072969 + 3 ^ 40 * 80493 * 2
def baseEnd_80493 : Nat := 24492799005901513758415

theorem tailTrace_80493 : CollatzResearch.WordTrace tailWord_80493 prefixEnd_80493 24492799005901513758415 := by
  unfold tailWord_80493
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935820897395082955046133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1957213931596721970030755 2935820897395082955046133)
  ·
    refine ⟨275233209130789027035575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2935820897395082955046133 275233209130789027035575)
    ·
      refine ⟨412849813696183540553363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275233209130789027035575 412849813696183540553363)
      ·
        refine ⟨619274720544275310830045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412849813696183540553363 619274720544275310830045)
        ·
          refine ⟨232228020204103241561267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 619274720544275310830045 232228020204103241561267)
          ·
            refine ⟨348342030306154862341901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232228020204103241561267 348342030306154862341901)
            ·
              refine ⟨130628261364808073378213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348342030306154862341901 130628261364808073378213)
              ·
                refine ⟨24492799005901513758415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130628261364808073378213 24492799005901513758415)
                ·
                  rfl

theorem cell19_80493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_80493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80493 prefixEnd_80493 := by exact prefixLift 80493
  have htrace : WordTrace (prefixWord ++ tailWord_80493) baseStart_80493 baseEnd_80493 := by
    simpa [prefixWord, tailWord_80493, baseEnd_80493] using wordTrace_append hprefix tailTrace_80493
  have hstable : (prefixWord ++ tailWord_80493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80493).length < 2 ^ (prefixWord ++ tailWord_80493).sum := by decide
  have hdescent : baseEnd_80493 < baseStart_80493 := by decide
  rcases family_descends (prefixWord ++ tailWord_80493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80495 : List Nat := [1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_80495 : Nat := 118140960795 + 80495 * 2 ^ 59
def prefixEnd_80495 : Nat := 4983230072969 + 3 ^ 40 * 80495 * 2
def baseEnd_80495 : Nat := 24493407575566101713965

theorem tailTrace_80495 : CollatzResearch.WordTrace tailWord_80495 prefixEnd_80495 24493407575566101713965 := by
  unfold tailWord_80495
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935893843387837296618939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1957262562258558197745959 2935893843387837296618939)
  ·
    refine ⟨4403840765081755944928409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2935893843387837296618939 4403840765081755944928409)
    ·
      refine ⟨3302880573811316958696307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4403840765081755944928409 3302880573811316958696307)
      ·
        refine ⟨4954320860716975438044461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302880573811316958696307 4954320860716975438044461)
        ·
          refine ⟨1857870322768865789266673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4954320860716975438044461 1857870322768865789266673)
          ·
            refine ⟨1393402742076649341950005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857870322768865789266673 1393402742076649341950005)
            ·
              refine ⟨130631507069685875807813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1393402742076649341950005 130631507069685875807813)
              ·
                refine ⟨24493407575566101713965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130631507069685875807813 24493407575566101713965)
                ·
                  rfl

theorem cell19_80495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_80495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80495 prefixEnd_80495 := by exact prefixLift 80495
  have htrace : WordTrace (prefixWord ++ tailWord_80495) baseStart_80495 baseEnd_80495 := by
    simpa [prefixWord, tailWord_80495, baseEnd_80495] using wordTrace_append hprefix tailTrace_80495
  have hstable : (prefixWord ++ tailWord_80495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80495).length < 2 ^ (prefixWord ++ tailWord_80495).sum := by decide
  have hdescent : baseEnd_80495 < baseStart_80495 := by decide
  rcases family_descends (prefixWord ++ tailWord_80495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80512 : List Nat := [2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_80512 : Nat := 118140960795 + 80512 * 2 ^ 59
def prefixEnd_80512 : Nat := 4983230072969 + 3 ^ 40 * 80512 * 2
def baseEnd_80512 : Nat := 24498580417715099336141

theorem tailTrace_80512 : CollatzResearch.WordTrace tailWord_80512 prefixEnd_80512 24498580417715099336141 := by
  unfold tailWord_80512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468256942163124599993895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1957675922884166133325193 1468256942163124599993895)
  ·
    refine ⟨2202385413244686899990843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468256942163124599993895 2202385413244686899990843)
    ·
      refine ⟨3303578119867030349986265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202385413244686899990843 3303578119867030349986265)
      ·
        refine ⟨2477683589900272762489699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3303578119867030349986265 2477683589900272762489699)
        ·
          refine ⟨3716525384850409143734549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477683589900272762489699 3716525384850409143734549)
          ·
            refine ⟨174212127414862928612557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3716525384850409143734549 174212127414862928612557)
            ·
              refine ⟨65329547780573598229709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174212127414862928612557 65329547780573598229709)
              ·
                refine ⟨24498580417715099336141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65329547780573598229709 24498580417715099336141)
                ·
                  rfl

theorem cell19_80512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_80512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80512 prefixEnd_80512 := by exact prefixLift 80512
  have htrace : WordTrace (prefixWord ++ tailWord_80512) baseStart_80512 baseEnd_80512 := by
    simpa [prefixWord, tailWord_80512, baseEnd_80512] using wordTrace_append hprefix tailTrace_80512
  have hstable : (prefixWord ++ tailWord_80512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80512).length < 2 ^ (prefixWord ++ tailWord_80512).sum := by decide
  have hdescent : baseEnd_80512 < baseStart_80512 := by decide
  rcases family_descends (prefixWord ++ tailWord_80512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80567 : List Nat := [1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_80567 : Nat := 118140960795 + 80567 * 2 ^ 59
def prefixEnd_80567 : Nat := 4983230072969 + 3 ^ 40 * 80567 * 2
def baseEnd_80567 : Nat := 24515316083491268113769

theorem tailTrace_80567 : CollatzResearch.WordTrace tailWord_80567 prefixEnd_80567 24515316083491268113769 := by
  unfold tailWord_80567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938519899126993593239955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1959013266084662395493303 2938519899126993593239955)
  ·
    refine ⟨4407779848690490389859933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938519899126993593239955 4407779848690490389859933)
    ·
      refine ⟨1652917443258933896197475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4407779848690490389859933 1652917443258933896197475)
      ·
        refine ⟨2479376164888400844296213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1652917443258933896197475 2479376164888400844296213)
        ·
          refine ⟨116220757729143789576385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2479376164888400844296213 116220757729143789576385)
          ·
            refine ⟨87165568296857842182289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116220757729143789576385 87165568296857842182289)
            ·
              refine ⟨65374176222643381636717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87165568296857842182289 65374176222643381636717)
              ·
                refine ⟨24515316083491268113769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65374176222643381636717 24515316083491268113769)
                ·
                  rfl

theorem cell19_80567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_80567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80567 prefixEnd_80567 := by exact prefixLift 80567
  have htrace : WordTrace (prefixWord ++ tailWord_80567) baseStart_80567 baseEnd_80567 := by
    simpa [prefixWord, tailWord_80567, baseEnd_80567] using wordTrace_append hprefix tailTrace_80567
  have hstable : (prefixWord ++ tailWord_80567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80567).length < 2 ^ (prefixWord ++ tailWord_80567).sum := by decide
  have hdescent : baseEnd_80567 < baseStart_80567 := by decide
  rcases family_descends (prefixWord ++ tailWord_80567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80582 : List Nat := [6, 1, 2, 1, 3, 1, 5]
def baseStart_80582 : Nat := 118140960795 + 80582 * 2 ^ 59
def prefixEnd_80582 : Nat := 4983230072969 + 3 ^ 40 * 80582 * 2
def baseEnd_80582 : Nat := 8173293451991892593465

theorem tailTrace_80582 : CollatzResearch.WordTrace tailWord_80582 prefixEnd_80582 8173293451991892593465 := by
  unfold tailWord_80582
  simp only [CollatzResearch.WordTrace]
  refine ⟨91845843564770348594875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1959377996048434103357333 91845843564770348594875)
  ·
    refine ⟨137768765347155522892313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91845843564770348594875 137768765347155522892313)
    ·
      refine ⟨103326574010366642169235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137768765347155522892313 103326574010366642169235)
      ·
        refine ⟨154989861015549963253853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103326574010366642169235 154989861015549963253853)
        ·
          refine ⟨58121197880831236220195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154989861015549963253853 58121197880831236220195)
          ·
            refine ⟨87181796821246854330293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58121197880831236220195 87181796821246854330293)
            ·
              refine ⟨8173293451991892593465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87181796821246854330293 8173293451991892593465)
              ·
                rfl

theorem cell19_80582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_80582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80582 prefixEnd_80582 := by exact prefixLift 80582
  have htrace : WordTrace (prefixWord ++ tailWord_80582) baseStart_80582 baseEnd_80582 := by
    simpa [prefixWord, tailWord_80582, baseEnd_80582] using wordTrace_append hprefix tailTrace_80582
  have hstable : (prefixWord ++ tailWord_80582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80582).length < 2 ^ (prefixWord ++ tailWord_80582).sum := by decide
  have hdescent : baseEnd_80582 < baseStart_80582 := by decide
  rcases family_descends (prefixWord ++ tailWord_80582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80588 : List Nat := [2, 2, 1, 5, 1, 3, 5]
def baseStart_80588 : Nat := 118140960795 + 80588 * 2 ^ 59
def prefixEnd_80588 : Nat := 4983230072969 + 3 ^ 40 * 80588 * 2
def baseEnd_80588 : Nat := 8173902021656480549015

theorem tailTrace_80588 : CollatzResearch.WordTrace tailWord_80588 prefixEnd_80588 8173902021656480549015 := by
  unfold tailWord_80588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469642916025457089877209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1959523888033942786502945 1469642916025457089877209)
  ·
    refine ⟨1102232187019092817407907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1469642916025457089877209 1102232187019092817407907)
    ·
      refine ⟨1653348280528639226111861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102232187019092817407907 1653348280528639226111861)
      ·
        refine ⟨155001401299559927447987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1653348280528639226111861 155001401299559927447987)
        ·
          refine ⟨232502101949339891171981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155001401299559927447987 232502101949339891171981)
          ·
            refine ⟨87188288231002459189493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232502101949339891171981 87188288231002459189493)
            ·
              refine ⟨8173902021656480549015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87188288231002459189493 8173902021656480549015)
              ·
                rfl

theorem cell19_80588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_80588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80588 prefixEnd_80588 := by exact prefixLift 80588
  have htrace : WordTrace (prefixWord ++ tailWord_80588) baseStart_80588 baseEnd_80588 := by
    simpa [prefixWord, tailWord_80588, baseEnd_80588] using wordTrace_append hprefix tailTrace_80588
  have hstable : (prefixWord ++ tailWord_80588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80588).length < 2 ^ (prefixWord ++ tailWord_80588).sum := by decide
  have hdescent : baseEnd_80588 < baseStart_80588 := by decide
  rcases family_descends (prefixWord ++ tailWord_80588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80590 : List Nat := [4, 1, 1, 1, 3, 2, 7]
def baseStart_80590 : Nat := 118140960795 + 80590 * 2 ^ 59
def prefixEnd_80590 : Nat := 4983230072969 + 3 ^ 40 * 80590 * 2
def baseEnd_80590 : Nat := 8174104878211343200865

theorem tailTrace_80590 : CollatzResearch.WordTrace tailWord_80590 prefixEnd_80590 8174104878211343200865 := by
  unfold tailWord_80590
  simp only [CollatzResearch.WordTrace]
  refine ⟨367419847255458565165903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1959572518695779014218149 367419847255458565165903)
  ·
    refine ⟨551129770883187847748855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367419847255458565165903 551129770883187847748855)
    ·
      refine ⟨826694656324781771623283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551129770883187847748855 826694656324781771623283)
      ·
        refine ⟨1240041984487172657434925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826694656324781771623283 1240041984487172657434925)
        ·
          refine ⟨465015744182689746538097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1240041984487172657434925 465015744182689746538097)
          ·
            refine ⟨348761808137017309903573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465015744182689746538097 348761808137017309903573)
            ·
              refine ⟨8174104878211343200865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 348761808137017309903573 8174104878211343200865)
              ·
                rfl

theorem cell19_80590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_80590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80590 prefixEnd_80590 := by exact prefixLift 80590
  have htrace : WordTrace (prefixWord ++ tailWord_80590) baseStart_80590 baseEnd_80590 := by
    simpa [prefixWord, tailWord_80590, baseEnd_80590] using wordTrace_append hprefix tailTrace_80590
  have hstable : (prefixWord ++ tailWord_80590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80590).length < 2 ^ (prefixWord ++ tailWord_80590).sum := by decide
  have hdescent : baseEnd_80590 < baseStart_80590 := by decide
  rcases family_descends (prefixWord ++ tailWord_80590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80609 : List Nat := [1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_80609 : Nat := 118140960795 + 80609 * 2 ^ 59
def prefixEnd_80609 : Nat := 4983230072969 + 3 ^ 40 * 80609 * 2
def baseEnd_80609 : Nat := 24528096046447615180321

theorem tailTrace_80609 : CollatzResearch.WordTrace tailWord_80609 prefixEnd_80609 24528096046447615180321 := by
  unfold tailWord_80609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940051764974834766268881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1960034509983223177512587 2940051764974834766268881)
  ·
    refine ⟨2205038823731126074701661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2940051764974834766268881 2205038823731126074701661)
    ·
      refine ⟨826889558899172278013123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2205038823731126074701661 826889558899172278013123)
      ·
        refine ⟨1240334338348758417019685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826889558899172278013123 1240334338348758417019685)
        ·
          refine ⟨232562688440392203191191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1240334338348758417019685 232562688440392203191191)
          ·
            refine ⟨348844032660588304786787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232562688440392203191191 348844032660588304786787)
            ·
              refine ⟨523266048990882457180181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348844032660588304786787 523266048990882457180181)
              ·
                refine ⟨24528096046447615180321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 523266048990882457180181 24528096046447615180321)
                ·
                  rfl

theorem cell19_80609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_80609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80609 prefixEnd_80609 := by exact prefixLift 80609
  have htrace : WordTrace (prefixWord ++ tailWord_80609) baseStart_80609 baseEnd_80609 := by
    simpa [prefixWord, tailWord_80609, baseEnd_80609] using wordTrace_append hprefix tailTrace_80609
  have hstable : (prefixWord ++ tailWord_80609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80609).length < 2 ^ (prefixWord ++ tailWord_80609).sum := by decide
  have hdescent : baseEnd_80609 < baseStart_80609 := by decide
  rcases family_descends (prefixWord ++ tailWord_80609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80647 : List Nat := [1, 1, 4, 4, 1, 8]
def baseStart_80647 : Nat := 118140960795 + 80647 * 2 ^ 59
def prefixEnd_80647 : Nat := 4983230072969 + 3 ^ 40 * 80647 * 2
def baseEnd_80647 : Nat := 2726628763341642926197

theorem tailTrace_80647 : CollatzResearch.WordTrace tailWord_80647 prefixEnd_80647 2726628763341642926197 := by
  unfold tailWord_80647
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941437738837167256152195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1960958492558111504101463 2941437738837167256152195)
  ·
    refine ⟨4412156608255750884228293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2941437738837167256152195 4412156608255750884228293)
    ·
      refine ⟨827279364047953290792805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4412156608255750884228293 827279364047953290792805)
      ·
        refine ⟨155114880758991242023651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 827279364047953290792805 155114880758991242023651)
        ·
          refine ⟨232672321138486863035477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155114880758991242023651 232672321138486863035477)
          ·
            refine ⟨2726628763341642926197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 232672321138486863035477 2726628763341642926197)
            ·
              rfl

theorem cell19_80647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_80647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80647 prefixEnd_80647 := by exact prefixLift 80647
  have htrace : WordTrace (prefixWord ++ tailWord_80647) baseStart_80647 baseEnd_80647 := by
    simpa [prefixWord, tailWord_80647, baseEnd_80647] using wordTrace_append hprefix tailTrace_80647
  have hstable : (prefixWord ++ tailWord_80647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80647).length < 2 ^ (prefixWord ++ tailWord_80647).sum := by decide
  have hdescent : baseEnd_80647 < baseStart_80647 := by decide
  rcases family_descends (prefixWord ++ tailWord_80647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80702 : List Nat := [4, 2, 1, 2, 3, 1, 6]
def baseStart_80702 : Nat := 118140960795 + 80702 * 2 ^ 59
def prefixEnd_80702 : Nat := 4983230072969 + 3 ^ 40 * 80702 * 2
def baseEnd_80702 : Nat := 8185464845283651704467

theorem tailTrace_80702 : CollatzResearch.WordTrace tailWord_80702 prefixEnd_80702 8185464845283651704467 := by
  unfold tailWord_80702
  simp only [CollatzResearch.WordTrace]
  refine ⟨367930469204738956175545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1962295835758607766269573 367930469204738956175545)
  ·
    refine ⟨275947851903554217131659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 367930469204738956175545 275947851903554217131659)
    ·
      refine ⟨413921777855331325697489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275947851903554217131659 413921777855331325697489)
      ·
        refine ⟨310441333391498494273117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413921777855331325697489 310441333391498494273117)
        ·
          refine ⟨116415500021811935352419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310441333391498494273117 116415500021811935352419)
          ·
            refine ⟨174623250032717903028629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116415500021811935352419 174623250032717903028629)
            ·
              refine ⟨8185464845283651704467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174623250032717903028629 8185464845283651704467)
              ·
                rfl

theorem cell19_80702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_80702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80702 prefixEnd_80702 := by exact prefixLift 80702
  have htrace : WordTrace (prefixWord ++ tailWord_80702) baseStart_80702 baseEnd_80702 := by
    simpa [prefixWord, tailWord_80702, baseEnd_80702] using wordTrace_append hprefix tailTrace_80702
  have hstable : (prefixWord ++ tailWord_80702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80702).length < 2 ^ (prefixWord ++ tailWord_80702).sum := by decide
  have hdescent : baseEnd_80702 < baseStart_80702 := by decide
  rcases family_descends (prefixWord ++ tailWord_80702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80740 : List Nat := [2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_80740 : Nat := 118140960795 + 80740 * 2 ^ 59
def prefixEnd_80740 : Nat := 4983230072969 + 3 ^ 40 * 80740 * 2
def baseEnd_80740 : Nat := 24567957359478126268853

theorem tailTrace_80740 : CollatzResearch.WordTrace tailWord_80740 prefixEnd_80740 24567957359478126268853 := by
  unfold tailWord_80740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472414863750122069643837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1963219818333496092858449 1472414863750122069643837)
  ·
    refine ⟨552155573906295776116439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1472414863750122069643837 552155573906295776116439)
    ·
      refine ⟨828233360859443664174659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 552155573906295776116439 828233360859443664174659)
      ·
        refine ⟨1242350041289165496261989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828233360859443664174659 1242350041289165496261989)
        ·
          refine ⟨232940632741718530549123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1242350041289165496261989 232940632741718530549123)
          ·
            refine ⟨349410949112577795823685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232940632741718530549123 349410949112577795823685)
            ·
              refine ⟨65514552958608336716941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 349410949112577795823685 65514552958608336716941)
              ·
                refine ⟨24567957359478126268853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65514552958608336716941 24567957359478126268853)
                ·
                  rfl

theorem cell19_80740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_80740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80740 prefixEnd_80740 := by exact prefixLift 80740
  have htrace : WordTrace (prefixWord ++ tailWord_80740) baseStart_80740 baseEnd_80740 := by
    simpa [prefixWord, tailWord_80740, baseEnd_80740] using wordTrace_append hprefix tailTrace_80740
  have hstable : (prefixWord ++ tailWord_80740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80740).length < 2 ^ (prefixWord ++ tailWord_80740).sum := by decide
  have hdescent : baseEnd_80740 < baseStart_80740 := by decide
  rcases family_descends (prefixWord ++ tailWord_80740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80761 : List Nat := [1, 2, 1, 3, 2, 5, 5]
def baseStart_80761 : Nat := 118140960795 + 80761 * 2 ^ 59
def prefixEnd_80761 : Nat := 4983230072969 + 3 ^ 40 * 80761 * 2
def baseEnd_80761 : Nat := 8191449113652099934043

theorem tailTrace_80761 : CollatzResearch.WordTrace tailWord_80761 prefixEnd_80761 8191449113652099934043 := by
  unfold tailWord_80761
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945595660424164725802137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1963730440282776483868091 2945595660424164725802137)
  ·
    refine ⟨2209196745318123544351603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2945595660424164725802137 2209196745318123544351603)
    ·
      refine ⟨3313795117977185316527405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2209196745318123544351603 3313795117977185316527405)
      ·
        refine ⟨1242673169241444493697777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3313795117977185316527405 1242673169241444493697777)
        ·
          refine ⟨932004876931083370273333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1242673169241444493697777 932004876931083370273333)
          ·
            refine ⟨87375457212289065963125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 932004876931083370273333 87375457212289065963125)
            ·
              refine ⟨8191449113652099934043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87375457212289065963125 8191449113652099934043)
              ·
                rfl

theorem cell19_80761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_80761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80761 prefixEnd_80761 := by exact prefixLift 80761
  have htrace : WordTrace (prefixWord ++ tailWord_80761) baseStart_80761 baseEnd_80761 := by
    simpa [prefixWord, tailWord_80761, baseEnd_80761] using wordTrace_append hprefix tailTrace_80761
  have hstable : (prefixWord ++ tailWord_80761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80761).length < 2 ^ (prefixWord ++ tailWord_80761).sum := by decide
  have hdescent : baseEnd_80761 < baseStart_80761 := by decide
  rcases family_descends (prefixWord ++ tailWord_80761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80763 : List Nat := [1, 1, 1, 1, 1, 5, 9]
def baseStart_80763 : Nat := 118140960795 + 80763 * 2 ^ 59
def prefixEnd_80763 : Nat := 4983230072969 + 3 ^ 40 * 80763 * 2
def baseEnd_80763 : Nat := 8191651970206962585893

theorem tailTrace_80763 : CollatzResearch.WordTrace tailWord_80763 prefixEnd_80763 8191651970206962585893 := by
  unfold tailWord_80763
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945668606416919067374943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1963779070944612711583295 2945668606416919067374943)
  ·
    refine ⟨4418502909625378601062415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2945668606416919067374943 4418502909625378601062415)
    ·
      refine ⟨6627754364438067901593623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4418502909625378601062415 6627754364438067901593623)
      ·
        refine ⟨9941631546657101852390435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627754364438067901593623 9941631546657101852390435)
        ·
          refine ⟨14912447319985652778585653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9941631546657101852390435 14912447319985652778585653)
          ·
            refine ⟨1398041936248654947992405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14912447319985652778585653 1398041936248654947992405)
            ·
              refine ⟨8191651970206962585893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1398041936248654947992405 8191651970206962585893)
              ·
                rfl

theorem cell19_80763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_80763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80763 prefixEnd_80763 := by exact prefixLift 80763
  have htrace : WordTrace (prefixWord ++ tailWord_80763) baseStart_80763 baseEnd_80763 := by
    simpa [prefixWord, tailWord_80763, baseEnd_80763] using wordTrace_append hprefix tailTrace_80763
  have hstable : (prefixWord ++ tailWord_80763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80763).length < 2 ^ (prefixWord ++ tailWord_80763).sum := by decide
  have hdescent : baseEnd_80763 < baseStart_80763 := by decide
  rcases family_descends (prefixWord ++ tailWord_80763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
